import NetHack.Soko22Hazard87.AndIntroBlocks0393
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro98500 (p : Pattern) (ha : d237508 p = 1) (hb : d289960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237495 q = 1) (hb : d289947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237495, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98497 q ha hb
    | true =>
      simp only [d237495, d289947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237496 q = 1) (hb : d289948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237496, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237496, d289948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237503 q = 1) (hb : d289955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98499 q ha hb
    | true =>
      simp only [d237503, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237504 q = 1) (hb : d289956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237505 q = 1) (hb : d289957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237505, d289957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237505, d289957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237506 q = 1) (hb : d289958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237506, d289958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237506, d289958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237507 q = 1) (hb : d289959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237507, d289959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237507, d289959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237508 q = 1) (hb : d289960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237508, d289960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237508, d289960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98501 (p : Pattern) (ha : d237521 p = 1) (hb : d289968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237464 q = 1) (hb : d289921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237464, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237464, d289921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98455 q ha hb
  have h2 (q : Pattern) (ha : d237230 q = 1) (hb : d289725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237230, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98455 q ha hb
    | true =>
      simp only [d237230, d289725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237465 q = 1) (hb : d289922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237465, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237465, d289922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237231 q = 1) (hb : d289726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237231, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237231, d289726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237466 q = 1) (hb : d289923 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237466, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237466, d289923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237467 q = 1) (hb : d289924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237467, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237467, d289924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237468 q = 1) (hb : d289925 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d289925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98456 q ha hb
  have h8 (q : Pattern) (ha : d237235 q = 1) (hb : d289730 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98456 q ha hb
    | true =>
      simp only [d237235, d289730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237469 q = 1) (hb : d289926 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237469, d289926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237236 q = 1) (hb : d289731 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237236, d289731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237470 q = 1) (hb : d289927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237470, d289927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237471 q = 1) (hb : d289928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237471, d289928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237472 q = 1) (hb : d289929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237472, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237472, d289929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237516 q = 1) (hb : d289963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237516, d289963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237516, d289963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98474 q ha hb
  have h15 (q : Pattern) (ha : d237346 q = 1) (hb : d289818 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237346, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98474 q ha hb
    | true =>
      simp only [d237346, d289818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237517 q = 1) (hb : d289964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237517, d289964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237517, d289964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237347 q = 1) (hb : d289819 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237347, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237347, d289819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237518 q = 1) (hb : d289965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237518, d289965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237518, d289965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237519 q = 1) (hb : d289966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237519, d289966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237519, d289966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237520 q = 1) (hb : d289967 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237520, d289967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237520, d289967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237521 q = 1) (hb : d289968 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237521, d289968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237521, d289968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98502 (p : Pattern) (ha : d237527 p = 1) (hb : d289974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237522 q = 1) (hb : d289969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237522, d289969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237522, d289969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98476 q ha hb
  have h2 (q : Pattern) (ha : d237353 q = 1) (hb : d289825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237353, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98476 q ha hb
    | true =>
      simp only [d237353, d289825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237523 q = 1) (hb : d289970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237523, d289970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237523, d289970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237354 q = 1) (hb : d289826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237354, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237354, d289826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237524 q = 1) (hb : d289971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237524, d289971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237524, d289971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237525 q = 1) (hb : d289972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237525, d289972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237525, d289972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237526 q = 1) (hb : d289973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237526, d289973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237526, d289973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237527 q = 1) (hb : d289974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237527, d289974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237527, d289974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro98503 (p : Pattern) (ha : d237533 p = 1) (hb : d289980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237474 q = 1) (hb : d289931 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98492 q ha hb
    | true =>
      simp only [d237474, d289931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98494 q ha hb
  have h2 (q : Pattern) (ha : d237475 q = 1) (hb : d289932 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d289932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237476 q = 1) (hb : d289933 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d289933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237484 q = 1) (hb : d289936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98494 q ha hb
    | true =>
      simp only [d237484, d289936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98495 q ha hb
  have h5 (q : Pattern) (ha : d237485 q = 1) (hb : d289937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d289937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237486 q = 1) (hb : d289938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d289938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237487 q = 1) (hb : d289939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237487, d289939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237528 q = 1) (hb : d289975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237528, d289975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98501 q ha hb
    | true =>
      simp only [d237528, d289975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98502 q ha hb
  have h9 (q : Pattern) (ha : d237529 q = 1) (hb : d289976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237529, d289976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237529, d289976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237530 q = 1) (hb : d289977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237530, d289977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237530, d289977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237531 q = 1) (hb : d289978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237531, d289978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237531, d289978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237532 q = 1) (hb : d289979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237532, d289979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237532, d289979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237533 q = 1) (hb : d289980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237533, d289980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237533, d289980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro98504 (p : Pattern) (ha : d237539 p = 1) (hb : d289986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237534 q = 1) (hb : d289981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237534, d289981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98503 q ha hb
    | true =>
      simp only [d237534, d289981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237535 q = 1) (hb : d289982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237535, d289982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237535, d289982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237536 q = 1) (hb : d289983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237536, d289983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237536, d289983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237537 q = 1) (hb : d289984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237537, d289984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237537, d289984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237538 q = 1) (hb : d289985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237538, d289985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237538, d289985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237539 q = 1) (hb : d289986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237539, d289986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237539, d289986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98505 (p : Pattern) (ha : d237545 p = 1) (hb : d289992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237509 q = 1) (hb : d289961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237509, d289961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98498 q ha hb
    | true =>
      simp only [d237509, d289961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98500 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d289962 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d289962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237515, d289962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237540 q = 1) (hb : d289987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237540, d289987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98504 q ha hb
    | true =>
      simp only [d237540, d289987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237541 q = 1) (hb : d289988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237541, d289988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237541, d289988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237542 q = 1) (hb : d289989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d289989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d289989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237543 q = 1) (hb : d289990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d289990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d289990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237544 q = 1) (hb : d289991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d289991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d289991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237545 q = 1) (hb : d289992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d289992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d289992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98506 (p : Pattern) (ha : d237513 p = 1) (hb : d289997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237503 q = 1) (hb : d289955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98499 q ha hb
    | true =>
      simp only [d237503, d289955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237504 q = 1) (hb : d289956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d289956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237510 q = 1) (hb : d289994 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237510, d289994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237510, d289994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237511 q = 1) (hb : d289995 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237511, d289995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237511, d289995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237512 q = 1) (hb : d289996 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237512, d289996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237512, d289996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237513 q = 1) (hb : d289997 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237513, d289997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237513, d289997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98507 (p : Pattern) (ha : d237552 p = 1) (hb : d290003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237547 q = 1) (hb : d289998 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237547, d289998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98506 q ha hb
    | true =>
      simp only [d237547, d289998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237548 q = 1) (hb : d289999 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237548, d289999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237548, d289999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237549 q = 1) (hb : d290000 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237549, d290000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237549, d290000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237550 q = 1) (hb : d290001 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237550, d290001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237550, d290001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237551 q = 1) (hb : d290002 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237551, d290002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237551, d290002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237552 q = 1) (hb : d290003 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237552, d290003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237552, d290003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98508 (p : Pattern) (ha : d237558 p = 1) (hb : d290009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237282 q = 1) (hb : d289769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237282, d289769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237282, d289769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98463 q ha hb
  have h2 (q : Pattern) (ha : d237283 q = 1) (hb : d289770 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237283, d289770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237283, d289770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237292 q = 1) (hb : d289779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237292, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98463 q ha hb
    | true =>
      simp only [d237292, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98466 q ha hb
  have h4 (q : Pattern) (ha : d237293 q = 1) (hb : d289780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237293, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237293, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237294 q = 1) (hb : d289781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237294, d289781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237294, d289781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237398 q = 1) (hb : d289870 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d289870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98480 q ha hb
    | true =>
      simp only [d237398, d289870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98487 q ha hb
  have h7 (q : Pattern) (ha : d237411 q = 1) (hb : d289883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237411, d289883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98488 q ha hb
    | true =>
      simp only [d237411, d289883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98489 q ha hb
  have h8 (q : Pattern) (ha : d237412 q = 1) (hb : d289884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d289884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237412, d289884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237413 q = 1) (hb : d289885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d289885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237413, d289885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237414 q = 1) (hb : d289886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d289886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237414, d289886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237418 q = 1) (hb : d289890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d289890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237418, d289890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98490 q ha hb
  have h12 (q : Pattern) (ha : d237420 q = 1) (hb : d289892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237420, d289892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237420, d289892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98491 q ha hb
  have h13 (q : Pattern) (ha : d237421 q = 1) (hb : d289893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d289893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237421, d289893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237422 q = 1) (hb : d289894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d289894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237422, d289894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237423 q = 1) (hb : d289895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d289895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237423, d289895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237424 q = 1) (hb : d289896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d289896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237424, d289896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237546 q = 1) (hb : d289993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d289993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237546, d289993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98505 q ha hb
  have h18 (q : Pattern) (ha : d237553 q = 1) (hb : d290004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237553, d290004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237553, d290004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98507 q ha hb
  have h19 (q : Pattern) (ha : d237554 q = 1) (hb : d290005 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d290005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237554, d290005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237555 q = 1) (hb : d290006 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d290006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237555, d290006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237556 q = 1) (hb : d290007 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d290007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237556, d290007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237557 q = 1) (hb : d290008 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d290008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237557, d290008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237558 q = 1) (hb : d290009 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d290009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237558, d290009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98509 (p : Pattern) (ha : d237564 p = 1) (hb : d290015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d290010 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d290010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d290010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98508 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d290011 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d290011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d290011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d290012 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d290012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d290012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d290013 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d290013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d290013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d290014 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d290014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d290014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d290015 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d290015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d290015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98510 (p : Pattern) (ha : d237938 p = 1) (hb : d290021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d236679 q = 1) (hb : d289394 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236679, d289394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97089 q ha hb
    | true =>
      simp only [d236679, d289394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97136 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236874 q = 1) (hb : d289434 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236874, d289434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236874, d289434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97190 q ha hb
  have h3 (q : Pattern) (ha : d236875 q = 1) (hb : d289435 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236875, d289435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236875, d289435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d289695 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d289695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d289695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98450 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d289696 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d289696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d289696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d289697 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d289697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237179, d289697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d290016 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d290016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d290016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98509 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d290017 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d290017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d290017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d290018 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d290018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d290018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d290019 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d290019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d290019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d239076 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d239076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d239076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91555 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d239077 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d239077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d239077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d239078 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d239078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d239078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d239079 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d239079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d239079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d290020 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d290020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d290020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d290021 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d290021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d290021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro98511 (p : Pattern) (ha : d237944 p = 1) (hb : d290027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d290022 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d290022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98510 q ha hb
    | true =>
      simp only [d237939, d290022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d290023 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d290023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d290023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d290024 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d290024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d290024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d290025 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d290025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d290025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d290026 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d290026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d290026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d290027 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d290027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d290027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98512 (p : Pattern) (ha : d237950 p = 1) (hb : d290033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d290028 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d290028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98511 q ha hb
    | true =>
      simp only [d237945, d290028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d290029 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d290029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d290029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d290030 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d290030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d290030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d290031 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d290031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d290031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d290032 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d290032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d290032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d290033 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d290033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d290033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98513 (p : Pattern) (ha : d237956 p = 1) (hb : d290039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d290034 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d290034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98512 q ha hb
    | true =>
      simp only [d237951, d290034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d290035 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d290035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d290035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d290036 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d290036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d290036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d290037 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d290037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d290037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d290038 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d290038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d290038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d290039 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d290039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d290039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98514 (p : Pattern) (ha : d237962 p = 1) (hb : d290045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d290040 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d290040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98513 q ha hb
    | true =>
      simp only [d237957, d290040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d290041 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d290041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d290041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d290042 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d290042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d290042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d290043 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d290043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d290043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d290044 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d290044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d290044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d290045 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d290045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d290045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98515 (p : Pattern) (ha : d237968 p = 1) (hb : d290051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d290046 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d290046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98514 q ha hb
    | true =>
      simp only [d237963, d290046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d290047 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d290047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d290047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d290048 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d290048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d290048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d290049 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d290049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d290049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d290050 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d290050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d290050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d290051 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d290051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d290051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98516 (p : Pattern) (ha : d237974 p = 1) (hb : d290057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d290052 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d290052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98515 q ha hb
    | true =>
      simp only [d237969, d290052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d290053 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d290053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d290053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d290054 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d290054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d290054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d290055 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d290055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d290055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d290056 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d290056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d290056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d290057 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d290057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d290057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98517 (p : Pattern) (ha : d237980 p = 1) (hb : d290063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d290058 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d290058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98516 q ha hb
    | true =>
      simp only [d237975, d290058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d290059 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d290059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d290059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d290060 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d290060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d290060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d290061 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d290061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d290061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d290062 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d290062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d290062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d290063 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d290063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d290063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98518 (p : Pattern) (ha : d287734 p = 1) (hb : d333402 p = 1) : d279879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39765 q = 1) (hb : d287734 q = 1) : d30172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d30172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98229 q ha hb
    | true =>
      simp only [d39765, d30172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98230 q ha hb
  have h2 (q : Pattern) (ha : d39766 q = 1) (hb : d287734 q = 1) : d30173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d30173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d30173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39767 q = 1) (hb : d287734 q = 1) : d30174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d30174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39767, d30174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39768 q = 1) (hb : d287734 q = 1) : d30175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d30175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d30175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39769 q = 1) (hb : d287734 q = 1) : d30176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d30176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d30176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d333402 q = 1) : d279879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333402, d279879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333402, d279879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98519 (p : Pattern) (ha : d287734 p = 1) (hb : d333413 p = 1) : d279890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d333408 q = 1) : d279885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333408, d279885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98267 q hb ha
    | true =>
      simp only [d333408, d279885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98238 q hb ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d333409 q = 1) : d279886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333409, d279886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333409, d279886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d333410 q = 1) : d279887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333410, d279887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333410, d279887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d333411 q = 1) : d279888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333411, d279888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333411, d279888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d333412 q = 1) : d279889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333412, d279889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333412, d279889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d333413 q = 1) : d279890 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333413, d279890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333413, d279890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98520 (p : Pattern) (ha : d287734 p = 1) (hb : d333419 p = 1) : d279896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d287734 q = 1) : d30178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d30178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98228 q ha hb
    | true =>
      simp only [d39771, d30178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98231 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d287734 q = 1) : d30179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d30179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, d30179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d333400 q = 1) : d279877 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, d279877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, d279877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d333401 q = 1) : d279878 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, d279878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, d279878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d333403 q = 1) : d279880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, d279880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, d279880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98518 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d333404 q = 1) : d279881 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, d279881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, d279881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d287734 q = 1) (hb : d333405 q = 1) : d279882 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, d279882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, d279882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d287734 q = 1) (hb : d333406 q = 1) : d279883 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, d279883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, d279883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d287734 q = 1) (hb : d333407 q = 1) : d279884 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, d279884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, d279884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287734 q = 1) (hb : d333414 q = 1) : d279891 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, d279891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, d279891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98519 q ha hb
  have h11 (q : Pattern) (ha : d287734 q = 1) (hb : d333415 q = 1) : d279892 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, d279892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, d279892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d287734 q = 1) (hb : d333416 q = 1) : d279893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, d279893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, d279893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d287734 q = 1) (hb : d333417 q = 1) : d279894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, d279894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, d279894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d287734 q = 1) (hb : d333418 q = 1) : d279895 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, d279895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, d279895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d287734 q = 1) (hb : d333419 q = 1) : d279896 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, d279896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, d279896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98521 (p : Pattern) (ha : d287734 p = 1) (hb : d333425 p = 1) : d279902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d333420 q = 1) : d279897 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, d279897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, d279897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98520 q ha hb
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d333421 q = 1) : d279898 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, d279898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, d279898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d333422 q = 1) : d279899 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, d279899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, d279899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d333423 q = 1) : d279900 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, d279900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, d279900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d333424 q = 1) : d279901 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, d279901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, d279901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d333425 q = 1) : d279902 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, d279902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, d279902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98522 (p : Pattern) (ha : d287734 p = 1) (hb : d338550 p = 1) : d290146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41239 q = 1) (hb : d287734 q = 1) : d289489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41239, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98289 q ha hb
    | true =>
      simp only [d41239, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98290 q ha hb
  have h2 (q : Pattern) (ha : d41240 q = 1) (hb : d287734 q = 1) : d289490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41240, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41240, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41241 q = 1) (hb : d287734 q = 1) : d289491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41241, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41241, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41242 q = 1) (hb : d287734 q = 1) : d289492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41242, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41242, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41243 q = 1) (hb : d287734 q = 1) : d289493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41243, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41243, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338550 q = 1) : d290146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338550, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338550, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98523 (p : Pattern) (ha : d287734 p = 1) (hb : d338561 p = 1) : d290157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338556 q = 1) : d290152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338556, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98324 q hb ha
    | true =>
      simp only [d338556, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98298 q hb ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338557 q = 1) : d290153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338557, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338557, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338558 q = 1) : d290154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338558, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338558, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338559 q = 1) : d290155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338559, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338559, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338560 q = 1) : d290156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338560, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338560, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338561 q = 1) : d290157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338561, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338561, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98524 (p : Pattern) (ha : d287734 p = 1) (hb : d338567 p = 1) : d290163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41245 q = 1) (hb : d287734 q = 1) : d289495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41245, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98288 q ha hb
    | true =>
      simp only [d41245, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98291 q ha hb
  have h2 (q : Pattern) (ha : d41246 q = 1) (hb : d287734 q = 1) : d289496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41246, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41246, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338548 q = 1) : d290144 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338548, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338548, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338549 q = 1) : d290145 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338549, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338549, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338551 q = 1) : d290147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338551, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338551, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98522 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338552 q = 1) : d290148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338552, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338552, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d287734 q = 1) (hb : d338553 q = 1) : d290149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338553, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338553, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d287734 q = 1) (hb : d338554 q = 1) : d290150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338554, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338554, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d287734 q = 1) (hb : d338555 q = 1) : d290151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338555, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338555, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287734 q = 1) (hb : d338562 q = 1) : d290158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338562, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338562, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98523 q ha hb
  have h11 (q : Pattern) (ha : d287734 q = 1) (hb : d338563 q = 1) : d290159 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338563, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338563, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d287734 q = 1) (hb : d338564 q = 1) : d290160 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338564, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338564, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d287734 q = 1) (hb : d338565 q = 1) : d290161 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338565, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338565, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d287734 q = 1) (hb : d338566 q = 1) : d290162 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338566, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338566, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d287734 q = 1) (hb : d338567 q = 1) : d290163 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338567, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338567, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98525 (p : Pattern) (ha : d287734 p = 1) (hb : d338573 p = 1) : d290169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338568 q = 1) : d290164 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338568, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338568, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98524 q ha hb
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338569 q = 1) : d290165 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338569, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338569, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338570 q = 1) : d290166 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338570, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338570, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338571 q = 1) : d290167 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338571, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338571, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338572 q = 1) : d290168 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338572, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338572, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338573 q = 1) : d290169 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338573, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338573, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98526 (p : Pattern) (ha : d287734 p = 1) (hb : d338579 p = 1) : d290175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41766 q = 1) (hb : d287734 q = 1) : d289773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41766, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98345 q ha hb
    | true =>
      simp only [d41766, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98346 q ha hb
  have h2 (q : Pattern) (ha : d41767 q = 1) (hb : d287734 q = 1) : d289774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41767, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41767, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41768 q = 1) (hb : d287734 q = 1) : d289775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41768, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41768, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41769 q = 1) (hb : d287734 q = 1) : d289776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41769, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41769, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41770 q = 1) (hb : d287734 q = 1) : d289777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41770, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41770, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338579 q = 1) : d290175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338579, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338579, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro98527 (p : Pattern) (ha : d287734 p = 1) (hb : d338590 p = 1) : d290186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338585 q = 1) : d290181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338585, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98383 q hb ha
    | true =>
      simp only [d338585, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98354 q hb ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338586 q = 1) : d290182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338586, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338586, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338587 q = 1) : d290183 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338587, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338587, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338588 q = 1) : d290184 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338588, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338588, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338589 q = 1) : d290185 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338589, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338589, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338590 q = 1) : d290186 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338590, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338590, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98528 (p : Pattern) (ha : d287734 p = 1) (hb : d338596 p = 1) : d290192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41772 q = 1) (hb : d287734 q = 1) : d289779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41772, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98344 q ha hb
    | true =>
      simp only [d41772, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98347 q ha hb
  have h2 (q : Pattern) (ha : d41773 q = 1) (hb : d287734 q = 1) : d289780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41773, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41773, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338577 q = 1) : d290173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338577, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338577, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338578 q = 1) : d290174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338578, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338578, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338580 q = 1) : d290176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338580, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338580, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98526 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338581 q = 1) : d290177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338581, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338581, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d287734 q = 1) (hb : d338582 q = 1) : d290178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338582, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338582, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d287734 q = 1) (hb : d338583 q = 1) : d290179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338583, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338583, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d287734 q = 1) (hb : d338584 q = 1) : d290180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338584, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338584, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287734 q = 1) (hb : d338591 q = 1) : d290187 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338591, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338591, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98527 q ha hb
  have h11 (q : Pattern) (ha : d287734 q = 1) (hb : d338592 q = 1) : d290188 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338592, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338592, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d287734 q = 1) (hb : d338593 q = 1) : d290189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338593, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338593, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d287734 q = 1) (hb : d338594 q = 1) : d290190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338594, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338594, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d287734 q = 1) (hb : d338595 q = 1) : d290191 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338595, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338595, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d287734 q = 1) (hb : d338596 q = 1) : d290192 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338596, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338596, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98529 (p : Pattern) (ha : d287734 p = 1) (hb : d338602 p = 1) : d290198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338597 q = 1) : d290193 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338597, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338597, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98528 q ha hb
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338598 q = 1) : d290194 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338598, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338598, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338599 q = 1) : d290195 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338599, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338599, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338600 q = 1) : d290196 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338600, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338600, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338601 q = 1) : d290197 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338601, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338601, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338602 q = 1) : d290198 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338602, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338602, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98530 (p : Pattern) (ha : d287734 p = 1) (hb : d338608 p = 1) : d290204 p = 1 := by
  have h0 (q : Pattern) (ha : d287734 q = 1) (hb : d290143 q = 1) : d290143 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338574 q = 1) : d290170 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338574, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338574, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98525 q ha hb
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338575 q = 1) : d290171 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338575, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338575, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338576 q = 1) : d290172 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338576, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d338576, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338603 q = 1) : d290199 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338603, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338603, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98529 q ha hb
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338604 q = 1) : d290200 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338604, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338604, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287734 q = 1) (hb : d338605 q = 1) : d290201 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338605, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338605, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287734 q = 1) (hb : d338606 q = 1) : d290202 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d338606, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338606, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287734 q = 1) (hb : d333426 q = 1) : d279903 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98521 q ha hb
  have h10 (q : Pattern) (ha : d287734 q = 1) (hb : d333427 q = 1) : d279904 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d287734 q = 1) (hb : d333428 q = 1) : d279905 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287734 q = 1) (hb : d333429 q = 1) : d279906 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d287734 q = 1) (hb : d338607 q = 1) : d290203 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d338607, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d338607, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d287734 q = 1) (hb : d338608 q = 1) : d290204 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d338608, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338608, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro98531 (p : Pattern) (ha : d287734 p = 1) (hb : d338614 p = 1) : d290210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338609 q = 1) : d290205 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d338609, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98530 q ha hb
    | true =>
      simp only [d338609, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338610 q = 1) : d290206 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d338610, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338610, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338611 q = 1) : d290207 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d338611, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338611, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338612 q = 1) : d290208 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d338612, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338612, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338613 q = 1) : d290209 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d338613, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338613, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287734 q = 1) (hb : d338614 q = 1) : d290210 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d338614, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338614, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98532 (p : Pattern) (ha : d287737 p = 1) (hb : d338620 p = 1) : d290216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287734 q = 1) (hb : d338615 q = 1) : d290211 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d338615, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98531 q ha hb
    | true =>
      simp only [d338615, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287734 q = 1) (hb : d338616 q = 1) : d290212 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d338616, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338616, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287734 q = 1) (hb : d338617 q = 1) : d290213 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d338617, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338617, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287734 q = 1) (hb : d338618 q = 1) : d290214 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d338618, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338618, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287734 q = 1) (hb : d338619 q = 1) : d290215 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d338619, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338619, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d287736 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d287737 q = 1) (hb : d338620 q = 1) : d290216 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d287737, d338620, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287737, d338620, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro98533 (p : Pattern) (ha : d287737 p = 1) (hb : d338626 p = 1) : d290222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287737 q = 1) (hb : d338621 q = 1) : d290217 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d338621, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98532 q ha hb
    | true =>
      simp only [d338621, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287737 q = 1) (hb : d338622 q = 1) : d290218 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d338622, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338622, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287737 q = 1) (hb : d338623 q = 1) : d290219 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d338623, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338623, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287737 q = 1) (hb : d338624 q = 1) : d290220 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d338624, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338624, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287737 q = 1) (hb : d338625 q = 1) : d290221 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d338625, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338625, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287737 q = 1) (hb : d338626 q = 1) : d290222 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d338626, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338626, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98534 (p : Pattern) (ha : d287737 p = 1) (hb : d338632 p = 1) : d290228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287737 q = 1) (hb : d338627 q = 1) : d290223 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d338627, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98533 q ha hb
    | true =>
      simp only [d338627, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287737 q = 1) (hb : d338628 q = 1) : d290224 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d338628, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338628, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287737 q = 1) (hb : d338629 q = 1) : d290225 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d338629, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338629, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287737 q = 1) (hb : d338630 q = 1) : d290226 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d338630, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338630, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287737 q = 1) (hb : d338631 q = 1) : d290227 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d338631, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338631, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287737 q = 1) (hb : d338632 q = 1) : d290228 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d338632, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338632, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98535 (p : Pattern) (ha : d287737 p = 1) (hb : d338638 p = 1) : d290234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287737 q = 1) (hb : d338633 q = 1) : d290229 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d338633, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98534 q ha hb
    | true =>
      simp only [d338633, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287737 q = 1) (hb : d338634 q = 1) : d290230 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d338634, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338634, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287737 q = 1) (hb : d338635 q = 1) : d290231 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d338635, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338635, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287737 q = 1) (hb : d338636 q = 1) : d290232 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d338636, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338636, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287737 q = 1) (hb : d338637 q = 1) : d290233 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d338637, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338637, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287737 q = 1) (hb : d338638 q = 1) : d290234 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d338638, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338638, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98536 (p : Pattern) (ha : d287737 p = 1) (hb : d338644 p = 1) : d290240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287737 q = 1) (hb : d338639 q = 1) : d290235 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d338639, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98535 q ha hb
    | true =>
      simp only [d338639, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287737 q = 1) (hb : d338640 q = 1) : d290236 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d338640, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338640, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287737 q = 1) (hb : d338641 q = 1) : d290237 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d338641, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338641, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287737 q = 1) (hb : d338642 q = 1) : d290238 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d338642, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338642, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287737 q = 1) (hb : d338643 q = 1) : d290239 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d338643, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338643, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287737 q = 1) (hb : d338644 q = 1) : d290240 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d338644, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338644, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98537 (p : Pattern) (ha : d287737 p = 1) (hb : d338650 p = 1) : d290246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287737 q = 1) (hb : d338645 q = 1) : d290241 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d338645, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98536 q ha hb
    | true =>
      simp only [d338645, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d287737 q = 1) (hb : d338646 q = 1) : d290242 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d338646, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338646, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d287737 q = 1) (hb : d338647 q = 1) : d290243 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d338647, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338647, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d287737 q = 1) (hb : d338648 q = 1) : d290244 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d338648, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338648, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d287737 q = 1) (hb : d338649 q = 1) : d290245 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d338649, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338649, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d287737 q = 1) (hb : d338650 q = 1) : d290246 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d338650, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338650, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98538 (p : Pattern) (ha : d237017 p = 1) (hb : d289484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d236930 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98406 q ha hb
    | true =>
      simp only [d236930, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98407 q ha hb
  have h5 (q : Pattern) (ha : d236998 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d236998, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237014 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237014, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237015 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237015, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237016 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237016, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237017 q = 1) (hb : d289484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237017, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237017, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98539 (p : Pattern) (ha : d237038 p = 1) (hb : d289494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236930 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98406 q ha hb
    | true =>
      simp only [d236930, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98407 q ha hb
  have h4 (q : Pattern) (ha : d236998 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236998, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237014 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237014, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237015 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237015, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237016 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237016, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237028 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d236940 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98409 q ha hb
    | true =>
      simp only [d236940, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98410 q ha hb
  have h13 (q : Pattern) (ha : d237031 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237031, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237035 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237035, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237036 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237036, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237036, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237037 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237037, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237037, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237038 q = 1) (hb : d289494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237038, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237038, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98540 (p : Pattern) (ha : d237058 p = 1) (hb : d290146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236940 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98409 q ha hb
    | true =>
      simp only [d236940, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98410 q ha hb
  have h3 (q : Pattern) (ha : d237031 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237031, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237035 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237035, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237056 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237056, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237056, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237057 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237057, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237057, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237058 q = 1) (hb : d290146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237058, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237058, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98541 (p : Pattern) (ha : d237157 p = 1) (hb : d290157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237137 q = 1) (hb : d290152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237137, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98442 q ha hb
    | true =>
      simp only [d237137, d290152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98447 q ha hb
  have h3 (q : Pattern) (ha : d237138 q = 1) (hb : d290153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237138, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237138, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237154 q = 1) (hb : d290154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237154, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237154, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237155 q = 1) (hb : d290155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237155, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237155, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237156 q = 1) (hb : d290156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237156, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237156, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237157 q = 1) (hb : d290157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237157, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237157, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98542 (p : Pattern) (ha : d237170 p = 1) (hb : d290163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237039 q = 1) (hb : d289495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237039, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98538 q ha hb
    | true =>
      simp only [d237039, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98539 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237053 q = 1) (hb : d289496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237053, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237053, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237054 q = 1) (hb : d290144 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237054, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237054, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237055 q = 1) (hb : d290145 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237055, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237055, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237059 q = 1) (hb : d290147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237059, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237059, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98540 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237061 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237062 q = 1) (hb : d290148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237062, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237062, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237063 q = 1) (hb : d290149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237063, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237063, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237064 q = 1) (hb : d290150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237064, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237064, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237065 q = 1) (hb : d290151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237065, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237065, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237158 q = 1) (hb : d290158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237158, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237158, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98541 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237166 q = 1) (hb : d290159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237166, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237166, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237167 q = 1) (hb : d290160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237167, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237167, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237168 q = 1) (hb : d290161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237168, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237168, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237169 q = 1) (hb : d290162 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237169, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237169, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237170 q = 1) (hb : d290163 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237170, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237170, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98543 (p : Pattern) (ha : d237176 p = 1) (hb : d290169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237171 q = 1) (hb : d290164 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237171, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237171, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98542 q ha hb
  have h2 (q : Pattern) (ha : d237172 q = 1) (hb : d290165 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237172, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237172, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237173 q = 1) (hb : d290166 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237173, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237173, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237174 q = 1) (hb : d290167 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237174, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237174, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237175 q = 1) (hb : d290168 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237175, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237175, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237176 q = 1) (hb : d290169 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237176, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237176, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98544 (p : Pattern) (ha : d237376 p = 1) (hb : d289768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237276 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98461 q ha hb
    | true =>
      simp only [d237276, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98462 q ha hb
  have h5 (q : Pattern) (ha : d237342 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237342, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237373 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237373, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237374 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237374, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237375 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237375, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237376 q = 1) (hb : d289768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237376, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237376, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98545 (p : Pattern) (ha : d237397 p = 1) (hb : d289778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237276 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98461 q ha hb
    | true =>
      simp only [d237276, d289763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98462 q ha hb
  have h4 (q : Pattern) (ha : d237342 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237342, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237373 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237373, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237374 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237374, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237375 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237375, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237286 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98464 q ha hb
    | true =>
      simp only [d237286, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98465 q ha hb
  have h13 (q : Pattern) (ha : d237390 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237390, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237394 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237394, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237395 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237395, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237395, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237396 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237396, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237396, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237397 q = 1) (hb : d289778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237397, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237397, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98546 (p : Pattern) (ha : d237417 p = 1) (hb : d290175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237286 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98464 q ha hb
    | true =>
      simp only [d237286, d289773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98465 q ha hb
  have h3 (q : Pattern) (ha : d237390 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237390, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237394 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237394, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237415 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237415, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237415, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237416 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237416, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237416, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237417 q = 1) (hb : d290175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237417, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237417, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98547 (p : Pattern) (ha : d237545 p = 1) (hb : d290186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237514 q = 1) (hb : d290181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237514, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98500 q ha hb
    | true =>
      simp only [d237514, d290181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98506 q ha hb
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d290182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237515, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237541 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237542 q = 1) (hb : d290183 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237543 q = 1) (hb : d290184 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237544 q = 1) (hb : d290185 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237545 q = 1) (hb : d290186 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98548 (p : Pattern) (ha : d237558 p = 1) (hb : d290192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237398 q = 1) (hb : d289779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98544 q ha hb
    | true =>
      simp only [d237398, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98545 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237412 q = 1) (hb : d289780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237412, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237413 q = 1) (hb : d290173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237413, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237414 q = 1) (hb : d290174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237414, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237418 q = 1) (hb : d290176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237418, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98546 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237421 q = 1) (hb : d290177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237421, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237422 q = 1) (hb : d290178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237422, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237423 q = 1) (hb : d290179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237423, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237424 q = 1) (hb : d290180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237424, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237546 q = 1) (hb : d290187 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237546, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98547 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237553 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237554 q = 1) (hb : d290188 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237554, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237555 q = 1) (hb : d290189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237555, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237556 q = 1) (hb : d290190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237556, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237557 q = 1) (hb : d290191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237557, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237558 q = 1) (hb : d290192 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237558, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98549 (p : Pattern) (ha : d237564 p = 1) (hb : d290198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d290193 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98548 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d290194 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d290195 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d290196 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d290197 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d290198 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98550 (p : Pattern) (ha : d237938 p = 1) (hb : d290204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d236679 q = 1) (hb : d290115 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236679, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97333 q ha hb
    | true =>
      simp only [d236679, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97339 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236874 q = 1) (hb : d290142 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236874, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236874, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97345 q ha hb
  have h3 (q : Pattern) (ha : d236875 q = 1) (hb : d290143 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236875, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236875, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d290170 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98543 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d290171 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d290172 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237179, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d290199 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98549 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d290200 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d290201 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d290202 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d279903 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91601 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d279904 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d279905 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d279906 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d290203 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d290204 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro98551 (p : Pattern) (ha : d237944 p = 1) (hb : d290210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d290205 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98550 q ha hb
    | true =>
      simp only [d237939, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d290206 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d290207 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d290208 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d290209 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d290210 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98552 (p : Pattern) (ha : d237950 p = 1) (hb : d290216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d290211 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98551 q ha hb
    | true =>
      simp only [d237945, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d290212 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d290213 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d290214 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d290215 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d290216 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98553 (p : Pattern) (ha : d237956 p = 1) (hb : d290222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d290217 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98552 q ha hb
    | true =>
      simp only [d237951, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d290218 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d290219 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d290220 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d290221 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d290222 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98554 (p : Pattern) (ha : d237962 p = 1) (hb : d290228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d290223 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98553 q ha hb
    | true =>
      simp only [d237957, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d290224 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d290225 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d290226 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d290227 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d290228 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98555 (p : Pattern) (ha : d237968 p = 1) (hb : d290234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d290229 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98554 q ha hb
    | true =>
      simp only [d237963, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d290230 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d290231 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d290232 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d290233 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d290234 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98556 (p : Pattern) (ha : d237974 p = 1) (hb : d290240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d290235 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98555 q ha hb
    | true =>
      simp only [d237969, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d290236 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d290237 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d290238 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d290239 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d290240 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98557 (p : Pattern) (ha : d237980 p = 1) (hb : d290246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d290241 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98556 q ha hb
    | true =>
      simp only [d237975, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d290242 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d290243 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d290244 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d290245 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d290246 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro98558 (p : Pattern) (ha : d238956 p = 1) (hb : d289484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238952 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238952, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238952, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238953 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238953, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238953, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238954 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238954, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238954, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238955 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238955, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238955, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238956 q = 1) (hb : d289484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238956, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238956, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98559 (p : Pattern) (ha : d238961 p = 1) (hb : d289494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289479 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238952 q = 1) (hb : d289480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238952, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238952, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238953 q = 1) (hb : d289481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238953, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238953, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238954 q = 1) (hb : d289482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238954, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238954, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238955 q = 1) (hb : d289483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238955, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238955, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29314 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29319 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238957 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238957, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238957, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238958 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238958, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238958, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238959 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238959, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d238959, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238960 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238960, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d238960, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238961 q = 1) (hb : d289494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238961, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238961, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98560 (p : Pattern) (ha : d238968 p = 1) (hb : d290146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289489 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238957 q = 1) (hb : d289490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238957, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238957, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238958 q = 1) (hb : d289491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238958, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238958, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238966 q = 1) (hb : d289492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238966, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238966, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238967 q = 1) (hb : d289493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238967, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238967, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238968 q = 1) (hb : d290146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238968, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238968, d290146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98561 (p : Pattern) (ha : d238978 p = 1) (hb : d290157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290152 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238974 q = 1) (hb : d290153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238974, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238974, d290153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29496 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238975 q = 1) (hb : d290154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238975, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238975, d290154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238976 q = 1) (hb : d290155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238976, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238976, d290155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238977 q = 1) (hb : d290156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238977, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238977, d290156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238978 q = 1) (hb : d290157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238978, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238978, d290157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98562 (p : Pattern) (ha : d238984 p = 1) (hb : d290163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238962 q = 1) (hb : d289495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238962, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98558 q ha hb
    | true =>
      simp only [d238962, d289495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98559 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238963 q = 1) (hb : d289496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238963, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238963, d289496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238964 q = 1) (hb : d290144 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238964, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238964, d290144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238965 q = 1) (hb : d290145 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238965, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238965, d290145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238969 q = 1) (hb : d290147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238969, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238969, d290147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98560 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29355 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238970 q = 1) (hb : d290148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238970, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238970, d290148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d238971 q = 1) (hb : d290149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238971, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238971, d290149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238972 q = 1) (hb : d290150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238972, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238972, d290150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238973 q = 1) (hb : d290151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238973, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238973, d290151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238979 q = 1) (hb : d290158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238979, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238979, d290158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98561 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29512 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238980 q = 1) (hb : d290159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238980, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238980, d290159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238981 q = 1) (hb : d290160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238981, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238981, d290160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238982 q = 1) (hb : d290161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238982, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238982, d290161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238983 q = 1) (hb : d290162 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238983, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238983, d290162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238984 q = 1) (hb : d290163 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238984, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238984, d290163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98563 (p : Pattern) (ha : d238990 p = 1) (hb : d290169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238985 q = 1) (hb : d290164 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238985, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238985, d290164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98562 q ha hb
  have h2 (q : Pattern) (ha : d238986 q = 1) (hb : d290165 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238986, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238986, d290165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238987 q = 1) (hb : d290166 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238987, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238987, d290166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238988 q = 1) (hb : d290167 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238988, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238988, d290167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238989 q = 1) (hb : d290168 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238989, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238989, d290168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238990 q = 1) (hb : d290169 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238990, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238990, d290169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98564 (p : Pattern) (ha : d238998 p = 1) (hb : d289768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238994 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238994, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238995 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238995, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238996 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238996, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238997 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238997, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238998 q = 1) (hb : d289768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238998, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238998, d289768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98565 (p : Pattern) (ha : d239003 p = 1) (hb : d289778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289763 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238994 q = 1) (hb : d289764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238994, d289764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238995 q = 1) (hb : d289765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238995, d289765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238996 q = 1) (hb : d289766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238996, d289766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238997 q = 1) (hb : d289767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238997, d289767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29826 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29831 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238999 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238999, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239000 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239000, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239001 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239001, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d239001, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d239002 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239002, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d239002, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d239003 q = 1) (hb : d289778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239003, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d239003, d289778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98566 (p : Pattern) (ha : d239010 p = 1) (hb : d290175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238999 q = 1) (hb : d289774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238999, d289774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239000 q = 1) (hb : d289775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239000, d289775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239008 q = 1) (hb : d289776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239008, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239008, d289776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239009 q = 1) (hb : d289777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239009, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239009, d289777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239010 q = 1) (hb : d290175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239010, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239010, d290175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98567 (p : Pattern) (ha : d239020 p = 1) (hb : d290186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239016 q = 1) (hb : d290182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239016, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239016, d290182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239017 q = 1) (hb : d290183 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239017, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239017, d290183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239018 q = 1) (hb : d290184 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239018, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239018, d290184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239019 q = 1) (hb : d290185 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239019, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239019, d290185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239020 q = 1) (hb : d290186 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239020, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239020, d290186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98568 (p : Pattern) (ha : d239026 p = 1) (hb : d290192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29641 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239004 q = 1) (hb : d289779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239004, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98564 q ha hb
    | true =>
      simp only [d239004, d289779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98565 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239005 q = 1) (hb : d289780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239005, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239005, d289780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239006 q = 1) (hb : d290173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239006, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239006, d290173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239007 q = 1) (hb : d290174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239007, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d239007, d290174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239011 q = 1) (hb : d290176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239011, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239011, d290176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98566 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29867 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d239012 q = 1) (hb : d290177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239012, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d239012, d290177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d239013 q = 1) (hb : d290178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239013, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d239013, d290178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d239014 q = 1) (hb : d290179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239014, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239014, d290179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d239015 q = 1) (hb : d290180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239015, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239015, d290180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239021 q = 1) (hb : d290187 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239021, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239021, d290187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98567 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239022 q = 1) (hb : d290188 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239022, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239022, d290188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239023 q = 1) (hb : d290189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239023, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239023, d290189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d239024 q = 1) (hb : d290190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239024, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d239024, d290190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d239025 q = 1) (hb : d290191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239025, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d239025, d290191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d239026 q = 1) (hb : d290192 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d239026, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d239026, d290192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98569 (p : Pattern) (ha : d239032 p = 1) (hb : d290198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239027 q = 1) (hb : d290193 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d239027, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239027, d290193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98568 q ha hb
  have h2 (q : Pattern) (ha : d239028 q = 1) (hb : d290194 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d239028, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239028, d290194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239029 q = 1) (hb : d290195 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d239029, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239029, d290195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239030 q = 1) (hb : d290196 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d239030, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239030, d290196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239031 q = 1) (hb : d290197 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d239031, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239031, d290197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239032 q = 1) (hb : d290198 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d239032, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239032, d290198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98570 (p : Pattern) (ha : d239081 p = 1) (hb : d290204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d238910 q = 1) (hb : d290115 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238910, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97371 q ha hb
    | true =>
      simp only [d238910, d290115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97377 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d238950 q = 1) (hb : d290142 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238950, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238950, d290142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97383 q ha hb
  have h3 (q : Pattern) (ha : d238951 q = 1) (hb : d290143 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238951, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238951, d290143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238991 q = 1) (hb : d290170 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238991, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238991, d290170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98563 q ha hb
  have h5 (q : Pattern) (ha : d238992 q = 1) (hb : d290171 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238992, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238992, d290171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238993 q = 1) (hb : d290172 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d238993, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238993, d290172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239033 q = 1) (hb : d290199 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d239033, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239033, d290199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98569 q ha hb
  have h8 (q : Pattern) (ha : d239034 q = 1) (hb : d290200 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d239034, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239034, d290200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d239035 q = 1) (hb : d290201 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d239035, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239035, d290201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239036 q = 1) (hb : d290202 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d239036, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239036, d290202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d239076 q = 1) (hb : d279903 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d239076, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239076, d279903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91627 q ha hb
  have h12 (q : Pattern) (ha : d239077 q = 1) (hb : d279904 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d239077, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239077, d279904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239078 q = 1) (hb : d279905 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d239078, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239078, d279905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239079 q = 1) (hb : d279906 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d239079, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239079, d279906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d239080 q = 1) (hb : d290203 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d239080, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239080, d290203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d239081 q = 1) (hb : d290204 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d239081, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239081, d290204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro98571 (p : Pattern) (ha : d239087 p = 1) (hb : d290210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239082 q = 1) (hb : d290205 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d239082, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98570 q ha hb
    | true =>
      simp only [d239082, d290205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239083 q = 1) (hb : d290206 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d239083, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239083, d290206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239084 q = 1) (hb : d290207 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d239084, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239084, d290207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239085 q = 1) (hb : d290208 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d239085, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239085, d290208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239086 q = 1) (hb : d290209 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d239086, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239086, d290209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239087 q = 1) (hb : d290210 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d239087, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239087, d290210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98572 (p : Pattern) (ha : d239093 p = 1) (hb : d290216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239088 q = 1) (hb : d290211 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d239088, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98571 q ha hb
    | true =>
      simp only [d239088, d290211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239089 q = 1) (hb : d290212 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d239089, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239089, d290212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239090 q = 1) (hb : d290213 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d239090, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239090, d290213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239091 q = 1) (hb : d290214 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d239091, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239091, d290214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239092 q = 1) (hb : d290215 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d239092, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239092, d290215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239093 q = 1) (hb : d290216 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d239093, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239093, d290216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98573 (p : Pattern) (ha : d239099 p = 1) (hb : d290222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239094 q = 1) (hb : d290217 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d239094, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98572 q ha hb
    | true =>
      simp only [d239094, d290217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239095 q = 1) (hb : d290218 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d239095, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239095, d290218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239096 q = 1) (hb : d290219 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d239096, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239096, d290219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239097 q = 1) (hb : d290220 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d239097, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239097, d290220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239098 q = 1) (hb : d290221 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d239098, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239098, d290221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239099 q = 1) (hb : d290222 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d239099, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239099, d290222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98574 (p : Pattern) (ha : d239105 p = 1) (hb : d290228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239100 q = 1) (hb : d290223 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d239100, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98573 q ha hb
    | true =>
      simp only [d239100, d290223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239101 q = 1) (hb : d290224 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d239101, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239101, d290224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239102 q = 1) (hb : d290225 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d239102, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239102, d290225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239103 q = 1) (hb : d290226 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d239103, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239103, d290226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239104 q = 1) (hb : d290227 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d239104, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239104, d290227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239105 q = 1) (hb : d290228 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d239105, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239105, d290228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98575 (p : Pattern) (ha : d239111 p = 1) (hb : d290234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239106 q = 1) (hb : d290229 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d239106, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98574 q ha hb
    | true =>
      simp only [d239106, d290229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239107 q = 1) (hb : d290230 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d239107, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239107, d290230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239108 q = 1) (hb : d290231 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d239108, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239108, d290231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239109 q = 1) (hb : d290232 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d239109, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239109, d290232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239110 q = 1) (hb : d290233 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d239110, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239110, d290233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239111 q = 1) (hb : d290234 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d239111, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239111, d290234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98576 (p : Pattern) (ha : d239117 p = 1) (hb : d290240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239112 q = 1) (hb : d290235 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d239112, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98575 q ha hb
    | true =>
      simp only [d239112, d290235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239113 q = 1) (hb : d290236 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d239113, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239113, d290236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239114 q = 1) (hb : d290237 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d239114, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239114, d290237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239115 q = 1) (hb : d290238 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d239115, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239115, d290238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239116 q = 1) (hb : d290239 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d239116, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239116, d290239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239117 q = 1) (hb : d290240 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d239117, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239117, d290240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98577 (p : Pattern) (ha : d239123 p = 1) (hb : d290246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239118 q = 1) (hb : d290241 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d239118, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98576 q ha hb
    | true =>
      simp only [d239118, d290241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239119 q = 1) (hb : d290242 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d239119, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239119, d290242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239120 q = 1) (hb : d290243 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d239120, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239120, d290243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239121 q = 1) (hb : d290244 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d239121, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239121, d290244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239122 q = 1) (hb : d290245 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d239122, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239122, d290245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239123 q = 1) (hb : d290246 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d239123, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239123, d290246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98578 (p : Pattern) (ha : d42249 p = 1) (hb : d310774 p = 1) : d310776 p = 1 := by
  have h0 (q : Pattern) (ha : d42247 q = 1) (hb : d271213 q = 1) : d42247 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42248 q = 1) (hb : d310774 q = 1) : d310775 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d310774, d310775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42248, d310774, d310775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d17 q = 1) (hb : d310774 q = 1) : d17 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42249 q = 1) (hb : d310774 q = 1) : d310776 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42249, d310776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42249, d310776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro98579 (p : Pattern) (ha : d42255 p = 1) (hb : d310774 p = 1) : d310782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d310774 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42253 q = 1) (hb : d310774 q = 1) : d310780 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42254 q = 1) (hb : d310774 q = 1) : d310781 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d310774 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d42255 q = 1) (hb : d310774 q = 1) : d310782 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42255, d310782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42255, d310782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98580 (p : Pattern) (ha : d42261 p = 1) (hb : d310774 p = 1) : d310788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42256 q = 1) (hb : d310774 q = 1) : d310783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
    | true =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42257 q = 1) (hb : d310774 q = 1) : d310784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42258 q = 1) (hb : d310774 q = 1) : d310785 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d310785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42258, d310785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42259 q = 1) (hb : d310774 q = 1) : d310786 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d310786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42259, d310786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d310774 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42260 q = 1) (hb : d310774 q = 1) : d310787 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42260, d310787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42260, d310787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d310774 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42261 q = 1) (hb : d310774 q = 1) : d310788 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42261, d310788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42261, d310788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98581 (p : Pattern) (ha : d42267 p = 1) (hb : d310774 p = 1) : d310794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d310774 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42262 q = 1) (hb : d310774 q = 1) : d310789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
    | true =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42263 q = 1) (hb : d310774 q = 1) : d310790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42264 q = 1) (hb : d310774 q = 1) : d310791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d310774 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42265 q = 1) (hb : d310774 q = 1) : d310792 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d310792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42265, d310792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d310774 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42266 q = 1) (hb : d310774 q = 1) : d310793 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42266, d310793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42266, d310793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42267 q = 1) (hb : d310774 q = 1) : d310794 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42267, d310794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42267, d310794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro98582 (p : Pattern) (ha : d42273 p = 1) (hb : d310774 p = 1) : d310800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d310774 q = 1) : d310798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42272 q = 1) (hb : d310774 q = 1) : d310799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d310799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d310799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42273 q = 1) (hb : d310774 q = 1) : d310800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42273, d310800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42273, d310800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98583 (p : Pattern) (ha : d309771 p = 1) (hb : d310774 p = 1) : d310806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d310774 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d310774 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d310774 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42274 q = 1) (hb : d310774 q = 1) : d310801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
    | true =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309767 q = 1) (hb : d310774 q = 1) : d310802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d310802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309767, d310802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d310774 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309768 q = 1) (hb : d310774 q = 1) : d310803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d310803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d310803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309769 q = 1) (hb : d310774 q = 1) : d310804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d310804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309769, d310804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309770 q = 1) (hb : d310774 q = 1) : d310805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d310805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309770, d310805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309771 q = 1) (hb : d310774 q = 1) : d310806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309771, d310806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309771, d310806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98584 (p : Pattern) (ha : d42280 p = 1) (hb : d310774 p = 1) : d310807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d310774 q = 1) : d310798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42272 q = 1) (hb : d310774 q = 1) : d310799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d310799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d310799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42280 q = 1) (hb : d310774 q = 1) : d310807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42280, d310807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42280, d310807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98585 (p : Pattern) (ha : d309776 p = 1) (hb : d310774 p = 1) : d310813 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d310774 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d310774 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d310774 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42274 q = 1) (hb : d310774 q = 1) : d310801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
    | true =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309767 q = 1) (hb : d310774 q = 1) : d310802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d310802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309767, d310802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d310774 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309768 q = 1) (hb : d310774 q = 1) : d310803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d310803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d310803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309769 q = 1) (hb : d310774 q = 1) : d310804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d310804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309769, d310804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309770 q = 1) (hb : d310774 q = 1) : d310805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d310805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309770, d310805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d310774 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d310774 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d310774 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d42281 q = 1) (hb : d310774 q = 1) : d310808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98584 q ha hb
    | true =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309772 q = 1) (hb : d310774 q = 1) : d310809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d310809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309772, d310809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d310774 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d309773 q = 1) (hb : d310774 q = 1) : d310810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d310810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309773, d310810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309774 q = 1) (hb : d310774 q = 1) : d310811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309774, d310811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309774, d310811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309775 q = 1) (hb : d310774 q = 1) : d310812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309775, d310812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309775, d310812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d309776 q = 1) (hb : d310774 q = 1) : d310813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309776, d310813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309776, d310813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98586 (p : Pattern) (ha : d309783 p = 1) (hb : d310774 p = 1) : d310820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d310774 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42281 q = 1) (hb : d310774 q = 1) : d310808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98584 q ha hb
    | true =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309772 q = 1) (hb : d310774 q = 1) : d310809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d310809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309772, d310809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d310774 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309773 q = 1) (hb : d310774 q = 1) : d310810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d310810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309773, d310810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309781 q = 1) (hb : d310774 q = 1) : d310818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309781, d310818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309781, d310818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309782 q = 1) (hb : d310774 q = 1) : d310819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309782, d310819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309782, d310819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309783 q = 1) (hb : d310774 q = 1) : d310820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309783, d310820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309783, d310820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98587 (p : Pattern) (ha : d42304 p = 1) (hb : d310774 p = 1) : d310831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42299 q = 1) (hb : d310774 q = 1) : d310826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d310826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42299, d310826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
  have h2 (q : Pattern) (ha : d42256 q = 1) (hb : d310774 q = 1) : d310783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
    | true =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42300 q = 1) (hb : d310774 q = 1) : d310827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d310827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42300, d310827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42257 q = 1) (hb : d310774 q = 1) : d310784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42301 q = 1) (hb : d310774 q = 1) : d310828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d310828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42301, d310828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42302 q = 1) (hb : d310774 q = 1) : d310829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d310829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42302, d310829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d310774 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42303 q = 1) (hb : d310774 q = 1) : d310830 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42303, d310830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42303, d310830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d310774 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42304 q = 1) (hb : d310774 q = 1) : d310831 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42304, d310831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42304, d310831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98588 (p : Pattern) (ha : d42310 p = 1) (hb : d310774 p = 1) : d310837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d310774 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42305 q = 1) (hb : d310774 q = 1) : d310832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
    | true =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42306 q = 1) (hb : d310774 q = 1) : d310833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42307 q = 1) (hb : d310774 q = 1) : d310834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d310774 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42308 q = 1) (hb : d310774 q = 1) : d310835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d310835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42308, d310835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d310774 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42309 q = 1) (hb : d310774 q = 1) : d310836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42309, d310836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42309, d310836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42310 q = 1) (hb : d310774 q = 1) : d310837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42310, d310837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42310, d310837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro98589 (p : Pattern) (ha : d42316 p = 1) (hb : d310774 p = 1) : d310843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42311 q = 1) (hb : d310774 q = 1) : d310838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98588 q ha hb
    | true =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42312 q = 1) (hb : d310774 q = 1) : d310839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d310774 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42313 q = 1) (hb : d310774 q = 1) : d310840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42313, d310840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42313, d310840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42314 q = 1) (hb : d310774 q = 1) : d310841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42314, d310841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42314, d310841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42315 q = 1) (hb : d310774 q = 1) : d310842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42315, d310842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42315, d310842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42316 q = 1) (hb : d310774 q = 1) : d310843 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42316, d310843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42316, d310843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98590 (p : Pattern) (ha : d309793 p = 1) (hb : d310774 p = 1) : d310849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d310774 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42317 q = 1) (hb : d310774 q = 1) : d310844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98589 q ha hb
    | true =>
      simp only [d42317, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309789 q = 1) (hb : d310774 q = 1) : d310845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309789, d310845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309789, d310845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d310774 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309790 q = 1) (hb : d310774 q = 1) : d310846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309790, d310846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309790, d310846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309791 q = 1) (hb : d310774 q = 1) : d310847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309791, d310847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309791, d310847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309792 q = 1) (hb : d310774 q = 1) : d310848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309792, d310848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309792, d310848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309793 q = 1) (hb : d310774 q = 1) : d310849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309793, d310849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309793, d310849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98591 (p : Pattern) (ha : d309799 p = 1) (hb : d310774 p = 1) : d310855 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d310774 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309777 q = 1) (hb : d310774 q = 1) : d310814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309777, d310814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98583 q ha hb
    | true =>
      simp only [d309777, d310814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98585 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d310774 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309778 q = 1) (hb : d310774 q = 1) : d310815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309778, d310815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309778, d310815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309779 q = 1) (hb : d310774 q = 1) : d310816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309779, d310816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309779, d310816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309780 q = 1) (hb : d310774 q = 1) : d310817 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309780, d310817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309780, d310817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309784 q = 1) (hb : d310774 q = 1) : d310821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309784, d310821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309784, d310821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98586 q ha hb
  have h8 (q : Pattern) (ha : d309785 q = 1) (hb : d310774 q = 1) : d310822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309785, d310822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309785, d310822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d309786 q = 1) (hb : d310774 q = 1) : d310823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309786, d310823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309786, d310823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d309787 q = 1) (hb : d310774 q = 1) : d310824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309787, d310824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309787, d310824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309788 q = 1) (hb : d310774 q = 1) : d310825 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309788, d310825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309788, d310825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309794 q = 1) (hb : d310774 q = 1) : d310850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309794, d310850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309794, d310850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98590 q ha hb
  have h13 (q : Pattern) (ha : d309795 q = 1) (hb : d310774 q = 1) : d310851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309795, d310851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309795, d310851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d309796 q = 1) (hb : d310774 q = 1) : d310852 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309796, d310852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309796, d310852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d309797 q = 1) (hb : d310774 q = 1) : d310853 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309797, d310853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309797, d310853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d309798 q = 1) (hb : d310774 q = 1) : d310854 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309798, d310854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309798, d310854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309799 q = 1) (hb : d310774 q = 1) : d310855 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309799, d310855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309799, d310855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro98592 (p : Pattern) (ha : d42338 p = 1) (hb : d310774 p = 1) : d310865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310774 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d310774 q = 1) : d310801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
    | true =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d310774 q = 1) : d310861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d310774 q = 1) : d310862 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d310774 q = 1) : d310863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d310774 q = 1) : d310864 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42338 q = 1) (hb : d310774 q = 1) : d310865 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42338, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42338, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98593 (p : Pattern) (ha : d42345 p = 1) (hb : d310774 p = 1) : d310872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310774 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d310774 q = 1) : d310801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
    | true =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d310774 q = 1) : d310861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d310774 q = 1) : d310862 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d310774 q = 1) : d310863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d310774 q = 1) : d310864 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d310774 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42281 q = 1) (hb : d310774 q = 1) : d310808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98584 q ha hb
    | true =>
      simp only [d42281, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42341 q = 1) (hb : d310774 q = 1) : d310868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42341, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42342 q = 1) (hb : d310774 q = 1) : d310869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42342, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42343 q = 1) (hb : d310774 q = 1) : d310870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42343, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42344 q = 1) (hb : d310774 q = 1) : d310871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42344, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42345 q = 1) (hb : d310774 q = 1) : d310872 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42345, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42345, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro98594 (p : Pattern) (ha : d42459 p = 1) (hb : d310774 p = 1) : d310954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d310774 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d310774 q = 1) : d310801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
    | true =>
      simp only [d42274, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d310774 q = 1) : d310861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d310774 q = 1) : d310862 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d310774 q = 1) : d310863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d310774 q = 1) : d310864 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d310774 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42459 q = 1) (hb : d310774 q = 1) : d310954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42459, d310954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42459, d310954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98595 (p : Pattern) (ha : d42350 p = 1) (hb : d310774 p = 1) : d310877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d310774 q = 1) : d310798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42349 q = 1) (hb : d310774 q = 1) : d310876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d310876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42349, d310876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42350 q = 1) (hb : d310774 q = 1) : d310877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42350, d310877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42350, d310877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98596 (p : Pattern) (ha : d42357 p = 1) (hb : d310774 p = 1) : d310884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42355 q = 1) (hb : d310774 q = 1) : d310882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d310882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42355, d310882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42356 q = 1) (hb : d310774 q = 1) : d310883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d310883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d310883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42357 q = 1) (hb : d310774 q = 1) : d310884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42357, d310884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42357, d310884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98597 (p : Pattern) (ha : d42363 p = 1) (hb : d310774 p = 1) : d310889 p = 1 := by
  have h0 (q : Pattern) (ha : d42361 q = 1) (hb : d271213 q = 1) : d42361 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42362 q = 1) (hb : d310774 q = 1) : d310888 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42362, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42362, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d42247 q = 1) (hb : d271213 q = 1) : d42247 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42248 q = 1) (hb : d310774 q = 1) : d310775 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d310774, d310775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42248, d310774, d310775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42363 q = 1) (hb : d310774 q = 1) : d310889 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42363, d310889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42363, d310889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98598 (p : Pattern) (ha : d42369 p = 1) (hb : d310774 p = 1) : d310895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d310774 q = 1) : d310892 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42367 q = 1) (hb : d310774 q = 1) : d310893 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42368 q = 1) (hb : d310774 q = 1) : d310894 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d310774 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42253 q = 1) (hb : d310774 q = 1) : d310780 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42254 q = 1) (hb : d310774 q = 1) : d310781 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42369 q = 1) (hb : d310774 q = 1) : d310895 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42369, d310895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42369, d310895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro98599 (p : Pattern) (ha : d42377 p = 1) (hb : d310774 p = 1) : d310903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42375 q = 1) (hb : d310774 q = 1) : d310901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42376 q = 1) (hb : d310774 q = 1) : d310902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d310774 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42377 q = 1) (hb : d310774 q = 1) : d310903 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42377, d310903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42377, d310903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98600 (p : Pattern) (ha : d42383 p = 1) (hb : d310774 p = 1) : d310909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42370 q = 1) (hb : d310774 q = 1) : d310896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
    | true =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42371 q = 1) (hb : d310774 q = 1) : d310897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42372 q = 1) (hb : d310774 q = 1) : d310898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d310898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42372, d310898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42373 q = 1) (hb : d310774 q = 1) : d310899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d310899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d310899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42256 q = 1) (hb : d310774 q = 1) : d310783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
    | true =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42257 q = 1) (hb : d310774 q = 1) : d310784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42258 q = 1) (hb : d310774 q = 1) : d310785 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d310785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42258, d310785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42259 q = 1) (hb : d310774 q = 1) : d310786 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d310786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42259, d310786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42374 q = 1) (hb : d310774 q = 1) : d310900 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42374, d310900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42374, d310900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42380 q = 1) (hb : d310774 q = 1) : d310906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42381 q = 1) (hb : d310774 q = 1) : d310907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d310774 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d42382 q = 1) (hb : d310774 q = 1) : d310908 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d310908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42382, d310908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42383 q = 1) (hb : d310774 q = 1) : d310909 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42383, d310909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42383, d310909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro98601 (p : Pattern) (ha : d42389 p = 1) (hb : d310774 p = 1) : d310915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42384 q = 1) (hb : d310774 q = 1) : d310910 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98600 q ha hb
    | true =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
  have h2 (q : Pattern) (ha : d42385 q = 1) (hb : d310774 q = 1) : d310911 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42386 q = 1) (hb : d310774 q = 1) : d310912 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d310774 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42262 q = 1) (hb : d310774 q = 1) : d310789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
    | true =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42263 q = 1) (hb : d310774 q = 1) : d310790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42264 q = 1) (hb : d310774 q = 1) : d310791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42387 q = 1) (hb : d310774 q = 1) : d310913 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d310774 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42265 q = 1) (hb : d310774 q = 1) : d310792 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d310792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42265, d310792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42388 q = 1) (hb : d310774 q = 1) : d310914 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42388, d310914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42388, d310914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42389 q = 1) (hb : d310774 q = 1) : d310915 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42389, d310915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42389, d310915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro98602 (p : Pattern) (ha : d42395 p = 1) (hb : d310774 p = 1) : d310921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42390 q = 1) (hb : d310774 q = 1) : d310916 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d310916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98601 q ha hb
    | true =>
      simp only [d42390, d310916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42391 q = 1) (hb : d310774 q = 1) : d310917 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d310917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42391, d310917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42392 q = 1) (hb : d310774 q = 1) : d310918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d310918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d310918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42393 q = 1) (hb : d310774 q = 1) : d310919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d310919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d310919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42394 q = 1) (hb : d310774 q = 1) : d310920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d310920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d310920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42395 q = 1) (hb : d310774 q = 1) : d310921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42395, d310921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42395, d310921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98603 (p : Pattern) (ha : d42430 p = 1) (hb : d310774 p = 1) : d310927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42427 q = 1) (hb : d310774 q = 1) : d310924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d310924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d310924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42428 q = 1) (hb : d310774 q = 1) : d310925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d310925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d310925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42429 q = 1) (hb : d310774 q = 1) : d310926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d310926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d310926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42430 q = 1) (hb : d310774 q = 1) : d310927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42430, d310927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42430, d310927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98604 (p : Pattern) (ha : d309809 p = 1) (hb : d310774 p = 1) : d310933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d310774 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42351 q = 1) (hb : d310774 q = 1) : d310878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d310878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98595 q ha hb
    | true =>
      simp only [d42351, d310878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42352 q = 1) (hb : d310774 q = 1) : d310879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d310879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42352, d310879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42353 q = 1) (hb : d310774 q = 1) : d310880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d310880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d310880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42354 q = 1) (hb : d310774 q = 1) : d310881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d310881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42354, d310881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d310774 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42358 q = 1) (hb : d310774 q = 1) : d310885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d310885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98596 q ha hb
    | true =>
      simp only [d42358, d310885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42359 q = 1) (hb : d310774 q = 1) : d310886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d310886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42359, d310886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42360 q = 1) (hb : d310774 q = 1) : d310887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d310887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d310887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42396 q = 1) (hb : d310774 q = 1) : d310922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d310922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98602 q ha hb
    | true =>
      simp only [d42396, d310922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
  have h11 (q : Pattern) (ha : d309805 q = 1) (hb : d310774 q = 1) : d310923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d310923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309805, d310923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42431 q = 1) (hb : d310774 q = 1) : d310928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d310928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98603 q ha hb
    | true =>
      simp only [d42431, d310928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42432 q = 1) (hb : d310774 q = 1) : d310929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d310929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d310929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d309806 q = 1) (hb : d310774 q = 1) : d310930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d310930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d310930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309807 q = 1) (hb : d310774 q = 1) : d310931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d310931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309807, d310931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309808 q = 1) (hb : d310774 q = 1) : d310932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d310932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309808, d310932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309809 q = 1) (hb : d310774 q = 1) : d310933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d310933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309809, d310933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro98605 (p : Pattern) (ha : d42437 p = 1) (hb : d310774 p = 1) : d310934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d310774 q = 1) : d310798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d310798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42349 q = 1) (hb : d310774 q = 1) : d310876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d310876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42349, d310876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42437 q = 1) (hb : d310774 q = 1) : d310934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42437, d310934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42437, d310934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98606 (p : Pattern) (ha : d42442 p = 1) (hb : d310774 p = 1) : d310939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d310774 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d310774 q = 1) : d310797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d310797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42355 q = 1) (hb : d310774 q = 1) : d310882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d310882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42355, d310882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42356 q = 1) (hb : d310774 q = 1) : d310883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d310883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d310883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42442 q = 1) (hb : d310774 q = 1) : d310939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42442, d310939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42442, d310939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98607 (p : Pattern) (ha : d42446 p = 1) (hb : d310774 p = 1) : d310943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42390 q = 1) (hb : d310774 q = 1) : d310916 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d310916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98601 q ha hb
    | true =>
      simp only [d42390, d310916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42391 q = 1) (hb : d310774 q = 1) : d310917 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d310917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42391, d310917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42392 q = 1) (hb : d310774 q = 1) : d310918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d310918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d310918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42393 q = 1) (hb : d310774 q = 1) : d310919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d310919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d310919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42394 q = 1) (hb : d310774 q = 1) : d310920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d310920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d310920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42446 q = 1) (hb : d310774 q = 1) : d310943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42446, d310943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42446, d310943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98608 (p : Pattern) (ha : d42451 p = 1) (hb : d310774 p = 1) : d310946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d310774 q = 1) : d310795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98581 q ha hb
    | true =>
      simp only [d42268, d310795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d310774 q = 1) : d310796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d310796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42427 q = 1) (hb : d310774 q = 1) : d310924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d310924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d310924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42428 q = 1) (hb : d310774 q = 1) : d310925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d310925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d310925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42429 q = 1) (hb : d310774 q = 1) : d310926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d310926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d310926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42451 q = 1) (hb : d310774 q = 1) : d310946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42451, d310946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42451, d310946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98609 (p : Pattern) (ha : d309814 p = 1) (hb : d310774 p = 1) : d310952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d310774 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42351 q = 1) (hb : d310774 q = 1) : d310878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d310878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98595 q ha hb
    | true =>
      simp only [d42351, d310878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42352 q = 1) (hb : d310774 q = 1) : d310879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d310879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42352, d310879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42353 q = 1) (hb : d310774 q = 1) : d310880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d310880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d310880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42354 q = 1) (hb : d310774 q = 1) : d310881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d310881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42354, d310881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d310774 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42358 q = 1) (hb : d310774 q = 1) : d310885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d310885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98596 q ha hb
    | true =>
      simp only [d42358, d310885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42359 q = 1) (hb : d310774 q = 1) : d310886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d310886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42359, d310886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42360 q = 1) (hb : d310774 q = 1) : d310887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d310887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d310887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42396 q = 1) (hb : d310774 q = 1) : d310922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d310922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98602 q ha hb
    | true =>
      simp only [d42396, d310922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98582 q ha hb
  have h11 (q : Pattern) (ha : d309805 q = 1) (hb : d310774 q = 1) : d310923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d310923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309805, d310923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42431 q = 1) (hb : d310774 q = 1) : d310928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d310928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98603 q ha hb
    | true =>
      simp only [d42431, d310928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42432 q = 1) (hb : d310774 q = 1) : d310929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d310929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d310929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d309806 q = 1) (hb : d310774 q = 1) : d310930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d310930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d310930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309807 q = 1) (hb : d310774 q = 1) : d310931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d310931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309807, d310931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309808 q = 1) (hb : d310774 q = 1) : d310932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d310932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309808, d310932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d310774 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d42438 q = 1) (hb : d310774 q = 1) : d310935 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42438, d310935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98605 q ha hb
    | true =>
      simp only [d42438, d310935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42439 q = 1) (hb : d310774 q = 1) : d310936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42439, d310936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42439, d310936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d42440 q = 1) (hb : d310774 q = 1) : d310937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42440, d310937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42440, d310937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d42441 q = 1) (hb : d310774 q = 1) : d310938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42441, d310938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42441, d310938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d310774 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d42443 q = 1) (hb : d310774 q = 1) : d310940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42443, d310940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98606 q ha hb
    | true =>
      simp only [d42443, d310940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d42444 q = 1) (hb : d310774 q = 1) : d310941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42444, d310941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42444, d310941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42445 q = 1) (hb : d310774 q = 1) : d310942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42445, d310942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42445, d310942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d42447 q = 1) (hb : d310774 q = 1) : d310944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d310944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98607 q ha hb
    | true =>
      simp only [d42447, d310944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98584 q ha hb
  have h27 (q : Pattern) (ha : d309810 q = 1) (hb : d310774 q = 1) : d310945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d310945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d309810, d310945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d42452 q = 1) (hb : d310774 q = 1) : d310947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d310947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98608 q ha hb
    | true =>
      simp only [d42452, d310947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d42453 q = 1) (hb : d310774 q = 1) : d310948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d310948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d42453, d310948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d309811 q = 1) (hb : d310774 q = 1) : d310949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d310949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d309811, d310949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d309812 q = 1) (hb : d310774 q = 1) : d310950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d310950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d309812, d310950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d309813 q = 1) (hb : d310774 q = 1) : d310951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d310951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309813, d310951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d309814 q = 1) (hb : d310774 q = 1) : d310952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d310952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309814, d310952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro98610 (p : Pattern) (ha : d309821 p = 1) (hb : d310774 p = 1) : d310961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42447 q = 1) (hb : d310774 q = 1) : d310944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d310944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98607 q ha hb
    | true =>
      simp only [d42447, d310944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98584 q ha hb
  have h2 (q : Pattern) (ha : d309810 q = 1) (hb : d310774 q = 1) : d310945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d310945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309810, d310945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42452 q = 1) (hb : d310774 q = 1) : d310947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d310947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98608 q ha hb
    | true =>
      simp only [d42452, d310947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42453 q = 1) (hb : d310774 q = 1) : d310948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d310948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42453, d310948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309811 q = 1) (hb : d310774 q = 1) : d310949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d310949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309811, d310949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309819 q = 1) (hb : d310774 q = 1) : d310959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d310959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309819, d310959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309820 q = 1) (hb : d310774 q = 1) : d310960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d310960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309820, d310960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309821 q = 1) (hb : d310774 q = 1) : d310961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d310961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309821, d310961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98611 (p : Pattern) (ha : d42482 p = 1) (hb : d310774 p = 1) : d310977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42472 q = 1) (hb : d310774 q = 1) : d310967 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d310967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42472, d310967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
  have h2 (q : Pattern) (ha : d42370 q = 1) (hb : d310774 q = 1) : d310896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
    | true =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42473 q = 1) (hb : d310774 q = 1) : d310968 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d310968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d310968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42371 q = 1) (hb : d310774 q = 1) : d310897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42474 q = 1) (hb : d310774 q = 1) : d310969 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d310969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d310969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42475 q = 1) (hb : d310774 q = 1) : d310970 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d310970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d310970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42299 q = 1) (hb : d310774 q = 1) : d310826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d310826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42299, d310826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
  have h8 (q : Pattern) (ha : d42256 q = 1) (hb : d310774 q = 1) : d310783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98579 q ha hb
    | true =>
      simp only [d42256, d310783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42300 q = 1) (hb : d310774 q = 1) : d310827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d310827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42300, d310827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42257 q = 1) (hb : d310774 q = 1) : d310784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42257, d310784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42301 q = 1) (hb : d310774 q = 1) : d310828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d310828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42301, d310828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42302 q = 1) (hb : d310774 q = 1) : d310829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d310829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42302, d310829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42476 q = 1) (hb : d310774 q = 1) : d310971 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42476, d310971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42476, d310971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42477 q = 1) (hb : d310774 q = 1) : d310972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
  have h15 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42478 q = 1) (hb : d310774 q = 1) : d310973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42479 q = 1) (hb : d310774 q = 1) : d310974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42480 q = 1) (hb : d310774 q = 1) : d310975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d310774 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d42481 q = 1) (hb : d310774 q = 1) : d310976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d310976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42481, d310976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d42482 q = 1) (hb : d310774 q = 1) : d310977 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42482, d310977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42482, d310977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro98612 (p : Pattern) (ha : d42488 p = 1) (hb : d310774 p = 1) : d310983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42483 q = 1) (hb : d310774 q = 1) : d310978 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98611 q ha hb
    | true =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
  have h2 (q : Pattern) (ha : d42484 q = 1) (hb : d310774 q = 1) : d310979 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42485 q = 1) (hb : d310774 q = 1) : d310980 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d310774 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42305 q = 1) (hb : d310774 q = 1) : d310832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
    | true =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42306 q = 1) (hb : d310774 q = 1) : d310833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42307 q = 1) (hb : d310774 q = 1) : d310834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42486 q = 1) (hb : d310774 q = 1) : d310981 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d310774 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42308 q = 1) (hb : d310774 q = 1) : d310835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d310835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42308, d310835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42487 q = 1) (hb : d310774 q = 1) : d310982 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42487, d310982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42487, d310982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42488 q = 1) (hb : d310774 q = 1) : d310983 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42488, d310983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42488, d310983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro98613 (p : Pattern) (ha : d42494 p = 1) (hb : d310774 p = 1) : d310989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42489 q = 1) (hb : d310774 q = 1) : d310984 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42489, d310984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98612 q ha hb
    | true =>
      simp only [d42489, d310984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42490 q = 1) (hb : d310774 q = 1) : d310985 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42490, d310985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42490, d310985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42311 q = 1) (hb : d310774 q = 1) : d310838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98588 q ha hb
    | true =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42312 q = 1) (hb : d310774 q = 1) : d310839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42491 q = 1) (hb : d310774 q = 1) : d310986 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42491, d310986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42491, d310986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42492 q = 1) (hb : d310774 q = 1) : d310987 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42492, d310987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42492, d310987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42493 q = 1) (hb : d310774 q = 1) : d310988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42493, d310988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42493, d310988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42494 q = 1) (hb : d310774 q = 1) : d310989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42494, d310989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42494, d310989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98614 (p : Pattern) (ha : d42519 p = 1) (hb : d310774 p = 1) : d310995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42311 q = 1) (hb : d310774 q = 1) : d310838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98588 q ha hb
    | true =>
      simp only [d42311, d310838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42312 q = 1) (hb : d310774 q = 1) : d310839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d310839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42516 q = 1) (hb : d310774 q = 1) : d310992 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42516, d310992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42516, d310992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42517 q = 1) (hb : d310774 q = 1) : d310993 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42517, d310993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42517, d310993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42518 q = 1) (hb : d310774 q = 1) : d310994 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42518, d310994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42518, d310994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42519 q = 1) (hb : d310774 q = 1) : d310995 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42519, d310995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42519, d310995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98615 (p : Pattern) (ha : d309831 p = 1) (hb : d310774 p = 1) : d311001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42495 q = 1) (hb : d310774 q = 1) : d310990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42495, d310990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98613 q ha hb
    | true =>
      simp only [d42495, d310990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98589 q ha hb
  have h2 (q : Pattern) (ha : d309827 q = 1) (hb : d310774 q = 1) : d310991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d310991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309827, d310991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42520 q = 1) (hb : d310774 q = 1) : d310996 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42520, d310996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98614 q ha hb
    | true =>
      simp only [d42520, d310996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42521 q = 1) (hb : d310774 q = 1) : d310997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42521, d310997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42521, d310997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309828 q = 1) (hb : d310774 q = 1) : d310998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d310998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309828, d310998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309829 q = 1) (hb : d310774 q = 1) : d310999 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d310999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309829, d310999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309830 q = 1) (hb : d310774 q = 1) : d311000 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d311000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309830, d311000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309831 q = 1) (hb : d310774 q = 1) : d311001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d311001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309831, d311001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98616 (p : Pattern) (ha : d309837 p = 1) (hb : d310774 p = 1) : d311007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42339 q = 1) (hb : d310774 q = 1) : d310866 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42339, d310866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42339, d310866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98592 q ha hb
  have h2 (q : Pattern) (ha : d42340 q = 1) (hb : d310774 q = 1) : d310867 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42340, d310867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42340, d310867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42346 q = 1) (hb : d310774 q = 1) : d310873 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98592 q ha hb
    | true =>
      simp only [d42346, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98593 q ha hb
  have h4 (q : Pattern) (ha : d42347 q = 1) (hb : d310774 q = 1) : d310874 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42347, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42348 q = 1) (hb : d310774 q = 1) : d310875 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42348, d310875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42348, d310875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309815 q = 1) (hb : d310774 q = 1) : d310953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d310953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98604 q ha hb
    | true =>
      simp only [d309815, d310953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98609 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d310774 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42460 q = 1) (hb : d310774 q = 1) : d310955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42460, d310955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98594 q ha hb
    | true =>
      simp only [d42460, d310955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309816 q = 1) (hb : d310774 q = 1) : d310956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d310956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309816, d310956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309817 q = 1) (hb : d310774 q = 1) : d310957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d310957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309817, d310957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d309818 q = 1) (hb : d310774 q = 1) : d310958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d310958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309818, d310958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309822 q = 1) (hb : d310774 q = 1) : d310962 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d310962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309822, d310962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98610 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d310774 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d309823 q = 1) (hb : d310774 q = 1) : d310963 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d310963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309823, d310963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309824 q = 1) (hb : d310774 q = 1) : d310964 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d310964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309824, d310964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d309825 q = 1) (hb : d310774 q = 1) : d310965 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d310965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309825, d310965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d309826 q = 1) (hb : d310774 q = 1) : d310966 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d310966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309826, d310966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309832 q = 1) (hb : d310774 q = 1) : d311002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d311002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309832, d311002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98615 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d310774 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d309833 q = 1) (hb : d310774 q = 1) : d311003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d311003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309833, d311003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d309834 q = 1) (hb : d310774 q = 1) : d311004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d311004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309834, d311004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d309835 q = 1) (hb : d310774 q = 1) : d311005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d311005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309835, d311005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d309836 q = 1) (hb : d310774 q = 1) : d311006 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d311006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309836, d311006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d309837 q = 1) (hb : d310774 q = 1) : d311007 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d311007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309837, d311007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro98617 (p : Pattern) (ha : d309843 p = 1) (hb : d310774 p = 1) : d311013 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d310774 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309800 q = 1) (hb : d310774 q = 1) : d310856 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309800, d310856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309800, d310856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98591 q ha hb
  have h3 (q : Pattern) (ha : d309801 q = 1) (hb : d310774 q = 1) : d310857 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309801, d310857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309801, d310857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309802 q = 1) (hb : d310774 q = 1) : d310858 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309802, d310858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309802, d310858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309803 q = 1) (hb : d310774 q = 1) : d310859 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309803, d310859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309803, d310859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309804 q = 1) (hb : d310774 q = 1) : d310860 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d310860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309804, d310860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309838 q = 1) (hb : d310774 q = 1) : d311008 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d311008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309838, d311008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98616 q ha hb
  have h8 (q : Pattern) (ha : d309839 q = 1) (hb : d310774 q = 1) : d311009 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d311009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309839, d311009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309840 q = 1) (hb : d310774 q = 1) : d311010 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d311010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309840, d311010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309841 q = 1) (hb : d310774 q = 1) : d311011 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d311011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309841, d311011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309842 q = 1) (hb : d310774 q = 1) : d311012 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d311012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309842, d311012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309843 q = 1) (hb : d310774 q = 1) : d311013 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d311013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309843, d311013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98618 (p : Pattern) (ha : d42540 p = 1) (hb : d310774 p = 1) : d311016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42384 q = 1) (hb : d310774 q = 1) : d310910 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98600 q ha hb
    | true =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
  have h2 (q : Pattern) (ha : d42385 q = 1) (hb : d310774 q = 1) : d310911 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42386 q = 1) (hb : d310774 q = 1) : d310912 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d310774 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42262 q = 1) (hb : d310774 q = 1) : d310789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
    | true =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42263 q = 1) (hb : d310774 q = 1) : d310790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42264 q = 1) (hb : d310774 q = 1) : d310791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42387 q = 1) (hb : d310774 q = 1) : d310913 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42538 q = 1) (hb : d310774 q = 1) : d311014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d311014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42538, d311014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42539 q = 1) (hb : d310774 q = 1) : d311015 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42539, d311015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42539, d311015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42540 q = 1) (hb : d310774 q = 1) : d311016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42540, d311016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42540, d311016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro98619 (p : Pattern) (ha : d42544 p = 1) (hb : d310774 p = 1) : d311020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d310774 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42262 q = 1) (hb : d310774 q = 1) : d310789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
    | true =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42263 q = 1) (hb : d310774 q = 1) : d310790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42264 q = 1) (hb : d310774 q = 1) : d310791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42538 q = 1) (hb : d310774 q = 1) : d311014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d311014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42538, d311014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42543 q = 1) (hb : d310774 q = 1) : d311019 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42543, d311019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42543, d311019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42544 q = 1) (hb : d310774 q = 1) : d311020 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42544, d311020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42544, d311020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98620 (p : Pattern) (ha : d42550 p = 1) (hb : d310774 p = 1) : d311026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d310774 q = 1) : d311024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42549 q = 1) (hb : d310774 q = 1) : d311025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d311025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d311025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42550 q = 1) (hb : d310774 q = 1) : d311026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42550, d311026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42550, d311026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98621 (p : Pattern) (ha : d42554 p = 1) (hb : d310774 p = 1) : d311030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d310774 q = 1) : d311028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42553 q = 1) (hb : d310774 q = 1) : d311029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d311029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d311029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42554 q = 1) (hb : d310774 q = 1) : d311030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42554, d311030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42554, d311030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98622 (p : Pattern) (ha : d42560 p = 1) (hb : d310774 p = 1) : d311036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d310774 q = 1) : d311031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98620 q ha hb
    | true =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98621 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d310774 q = 1) : d311032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d310774 q = 1) : d311033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d310774 q = 1) : d311034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d310774 q = 1) : d311035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42560 q = 1) (hb : d310774 q = 1) : d311036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42560, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42560, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98623 (p : Pattern) (ha : d42563 p = 1) (hb : d310774 p = 1) : d311039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d310774 q = 1) : d311024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42549 q = 1) (hb : d310774 q = 1) : d311025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d311025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d311025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42563 q = 1) (hb : d310774 q = 1) : d311039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42563, d311039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42563, d311039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98624 (p : Pattern) (ha : d42564 p = 1) (hb : d310774 p = 1) : d311040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d310774 q = 1) : d311028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42553 q = 1) (hb : d310774 q = 1) : d311029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d311029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d311029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42564 q = 1) (hb : d310774 q = 1) : d311040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42564, d311040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42564, d311040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98625 (p : Pattern) (ha : d42570 p = 1) (hb : d310774 p = 1) : d311046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d310774 q = 1) : d311031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98620 q ha hb
    | true =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98621 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d310774 q = 1) : d311032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d310774 q = 1) : d311033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d310774 q = 1) : d311034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d310774 q = 1) : d311035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42565 q = 1) (hb : d310774 q = 1) : d311041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98623 q ha hb
    | true =>
      simp only [d42565, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98624 q ha hb
  have h7 (q : Pattern) (ha : d42566 q = 1) (hb : d310774 q = 1) : d311042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42566, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42567 q = 1) (hb : d310774 q = 1) : d311043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42567, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42568 q = 1) (hb : d310774 q = 1) : d311044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42568, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42569 q = 1) (hb : d310774 q = 1) : d311045 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42569, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42570 q = 1) (hb : d310774 q = 1) : d311046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42570, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42570, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98626 (p : Pattern) (ha : d42730 p = 1) (hb : d310774 p = 1) : d311154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d310774 q = 1) : d311031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98620 q ha hb
    | true =>
      simp only [d42555, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98621 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d310774 q = 1) : d311032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d310774 q = 1) : d311033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d310774 q = 1) : d311034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d310774 q = 1) : d311035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42725 q = 1) (hb : d310774 q = 1) : d311149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d311149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98621 q ha hb
    | true =>
      simp only [d42725, d311149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42726 q = 1) (hb : d310774 q = 1) : d311150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d311150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42726, d311150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42727 q = 1) (hb : d310774 q = 1) : d311151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d311151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42727, d311151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42728 q = 1) (hb : d310774 q = 1) : d311152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d311152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42728, d311152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42729 q = 1) (hb : d310774 q = 1) : d311153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d311153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42729, d311153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42730 q = 1) (hb : d310774 q = 1) : d311154 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42730, d311154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42730, d311154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98627 (p : Pattern) (ha : d42736 p = 1) (hb : d310774 p = 1) : d311160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42725 q = 1) (hb : d310774 q = 1) : d311149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d311149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98621 q ha hb
    | true =>
      simp only [d42725, d311149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42726 q = 1) (hb : d310774 q = 1) : d311150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d311150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42726, d311150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42727 q = 1) (hb : d310774 q = 1) : d311151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d311151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42727, d311151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42728 q = 1) (hb : d310774 q = 1) : d311152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d311152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42728, d311152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42729 q = 1) (hb : d310774 q = 1) : d311153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d311153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42729, d311153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42731 q = 1) (hb : d310774 q = 1) : d311155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d311155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98624 q ha hb
    | true =>
      simp only [d42731, d311155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42732 q = 1) (hb : d310774 q = 1) : d311156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d311156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42732, d311156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42733 q = 1) (hb : d310774 q = 1) : d311157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d311157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42733, d311157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42734 q = 1) (hb : d310774 q = 1) : d311158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d311158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42734, d311158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42735 q = 1) (hb : d310774 q = 1) : d311159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d311159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42735, d311159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42736 q = 1) (hb : d310774 q = 1) : d311160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42736, d311160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42736, d311160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98628 (p : Pattern) (ha : d42745 p = 1) (hb : d310774 p = 1) : d311169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42731 q = 1) (hb : d310774 q = 1) : d311155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d311155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98624 q ha hb
    | true =>
      simp only [d42731, d311155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42732 q = 1) (hb : d310774 q = 1) : d311156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d311156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42732, d311156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42733 q = 1) (hb : d310774 q = 1) : d311157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d311157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42733, d311157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42734 q = 1) (hb : d310774 q = 1) : d311158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d311158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42734, d311158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42735 q = 1) (hb : d310774 q = 1) : d311159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d311159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42735, d311159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42745 q = 1) (hb : d310774 q = 1) : d311169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42745, d311169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42745, d311169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98629 (p : Pattern) (ha : d42788 p = 1) (hb : d310774 p = 1) : d311212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d310774 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42305 q = 1) (hb : d310774 q = 1) : d310832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
    | true =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42306 q = 1) (hb : d310774 q = 1) : d310833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42307 q = 1) (hb : d310774 q = 1) : d310834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42778 q = 1) (hb : d310774 q = 1) : d311202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d311202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42778, d311202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42787 q = 1) (hb : d310774 q = 1) : d311211 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42787, d311211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42787, d311211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42788 q = 1) (hb : d310774 q = 1) : d311212 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42788, d311212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42788, d311212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro98630 (p : Pattern) (ha : d42844 p = 1) (hb : d310774 p = 1) : d311235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42789 q = 1) (hb : d310774 q = 1) : d311213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d311213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98629 q ha hb
    | true =>
      simp only [d42789, d311213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42790 q = 1) (hb : d310774 q = 1) : d311214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d311214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42790, d311214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42841 q = 1) (hb : d310774 q = 1) : d311232 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42841, d311232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42841, d311232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42842 q = 1) (hb : d310774 q = 1) : d311233 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42842, d311233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42842, d311233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42843 q = 1) (hb : d310774 q = 1) : d311234 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42843, d311234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42843, d311234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42844 q = 1) (hb : d310774 q = 1) : d311235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42844, d311235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42844, d311235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98631 (p : Pattern) (ha : d42850 p = 1) (hb : d310774 p = 1) : d311241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42845 q = 1) (hb : d310774 q = 1) : d311236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42845, d311236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98630 q ha hb
    | true =>
      simp only [d42845, d311236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42846 q = 1) (hb : d310774 q = 1) : d311237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42846, d311237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42846, d311237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42847 q = 1) (hb : d310774 q = 1) : d311238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42847, d311238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42847, d311238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42848 q = 1) (hb : d310774 q = 1) : d311239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42848, d311239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42848, d311239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42849 q = 1) (hb : d310774 q = 1) : d311240 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42849, d311240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42849, d311240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42850 q = 1) (hb : d310774 q = 1) : d311241 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42850, d311241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42850, d311241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98632 (p : Pattern) (ha : d42575 p = 1) (hb : d310774 p = 1) : d311051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d310774 q = 1) : d311024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42574 q = 1) (hb : d310774 q = 1) : d311050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d311050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42574, d311050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42575 q = 1) (hb : d310774 q = 1) : d311051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42575, d311051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42575, d311051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98633 (p : Pattern) (ha : d42577 p = 1) (hb : d310774 p = 1) : d311053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d310774 q = 1) : d311028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42576 q = 1) (hb : d310774 q = 1) : d311052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d311052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42576, d311052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42577 q = 1) (hb : d310774 q = 1) : d311053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42577, d311053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42577, d311053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98634 (p : Pattern) (ha : d42584 p = 1) (hb : d310774 p = 1) : d311060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42582 q = 1) (hb : d310774 q = 1) : d311058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d311058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42582, d311058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42583 q = 1) (hb : d310774 q = 1) : d311059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d311059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d311059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42584 q = 1) (hb : d310774 q = 1) : d311060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42584, d311060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42584, d311060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98635 (p : Pattern) (ha : d42587 p = 1) (hb : d310774 p = 1) : d311063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42585 q = 1) (hb : d310774 q = 1) : d311061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d311061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42585, d311061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42586 q = 1) (hb : d310774 q = 1) : d311062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d311062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d311062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42587 q = 1) (hb : d310774 q = 1) : d311063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42587, d311063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42587, d311063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98636 (p : Pattern) (ha : d42594 p = 1) (hb : d310774 p = 1) : d311068 p = 1 := by
  have h0 (q : Pattern) (ha : d2001 q = 1) (hb : d271213 q = 1) : d2001 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34366 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42591 q = 1) (hb : d310774 q = 1) : d2002 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, d310774, d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42591, d310774, d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d42592 q = 1) (hb : d271213 q = 1) : d42592 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42247 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42593 q = 1) (hb : d310774 q = 1) : d311067 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42593, d310774, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42593, d310774, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42594 q = 1) (hb : d310774 q = 1) : d311068 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42594, d311068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42594, d311068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98637 (p : Pattern) (ha : d42601 p = 1) (hb : d310774 p = 1) : d311073 p = 1 := by
  have h0 (q : Pattern) (ha : d42361 q = 1) (hb : d271213 q = 1) : d42361 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42599 q = 1) (hb : d310774 q = 1) : d310888 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42599, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42599, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d42598 q = 1) (hb : d271213 q = 1) : d42598 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42600 q = 1) (hb : d310774 q = 1) : d311072 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d310774, d311072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42600, d310774, d311072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42601 q = 1) (hb : d310774 q = 1) : d311073 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42601, d311073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42601, d311073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98638 (p : Pattern) (ha : d42607 p = 1) (hb : d310774 p = 1) : d311079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d310774 q = 1) : d311069 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d310774 q = 1) : d311070 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42597 q = 1) (hb : d310774 q = 1) : d311071 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d310774 q = 1) : d311074 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98637 q ha hb
    | true =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d310774 q = 1) : d311075 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d310774 q = 1) : d311076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42605 q = 1) (hb : d310774 q = 1) : d311077 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d311077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d311077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42606 q = 1) (hb : d310774 q = 1) : d311078 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d311078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d311078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42366 q = 1) (hb : d310774 q = 1) : d310892 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42367 q = 1) (hb : d310774 q = 1) : d310893 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42368 q = 1) (hb : d310774 q = 1) : d310894 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42607 q = 1) (hb : d310774 q = 1) : d311079 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42607, d311079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42607, d311079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98639 (p : Pattern) (ha : d42612 p = 1) (hb : d310774 p = 1) : d311084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d310774 q = 1) : d310892 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42367 q = 1) (hb : d310774 q = 1) : d310893 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d310893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42368 q = 1) (hb : d310774 q = 1) : d310894 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d310894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42375 q = 1) (hb : d310774 q = 1) : d310901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42376 q = 1) (hb : d310774 q = 1) : d310902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42612 q = 1) (hb : d310774 q = 1) : d311084 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42612, d311084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42612, d311084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98640 (p : Pattern) (ha : d42620 p = 1) (hb : d310774 p = 1) : d311092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d310774 q = 1) : d310892 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d310892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42618 q = 1) (hb : d310774 q = 1) : d311090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42618, d311090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42618, d311090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42619 q = 1) (hb : d310774 q = 1) : d311091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42619, d311091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42619, d311091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42375 q = 1) (hb : d310774 q = 1) : d310901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42375, d310901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42376 q = 1) (hb : d310774 q = 1) : d310902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d310902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42620 q = 1) (hb : d310774 q = 1) : d311092 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42620, d311092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42620, d311092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro98641 (p : Pattern) (ha : d42626 p = 1) (hb : d310774 p = 1) : d311098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42608 q = 1) (hb : d310774 q = 1) : d311080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
    | true =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42609 q = 1) (hb : d310774 q = 1) : d311081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42610 q = 1) (hb : d310774 q = 1) : d311082 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d311082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42610, d311082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42611 q = 1) (hb : d310774 q = 1) : d311083 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d311083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d311083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42613 q = 1) (hb : d310774 q = 1) : d311085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
    | true =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42614 q = 1) (hb : d310774 q = 1) : d311086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42615 q = 1) (hb : d310774 q = 1) : d311087 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d311087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42615, d311087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42616 q = 1) (hb : d310774 q = 1) : d311088 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d311088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d311088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42617 q = 1) (hb : d310774 q = 1) : d311089 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d311089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d311089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42623 q = 1) (hb : d310774 q = 1) : d311095 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42624 q = 1) (hb : d310774 q = 1) : d311096 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42380 q = 1) (hb : d310774 q = 1) : d310906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42381 q = 1) (hb : d310774 q = 1) : d310907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42625 q = 1) (hb : d310774 q = 1) : d311097 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42625, d311097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42625, d311097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42626 q = 1) (hb : d310774 q = 1) : d311098 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42626, d311098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42626, d311098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98642 (p : Pattern) (ha : d42630 p = 1) (hb : d310774 p = 1) : d311102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42380 q = 1) (hb : d310774 q = 1) : d310906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d310906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42381 q = 1) (hb : d310774 q = 1) : d310907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42381, d310907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d310774 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42382 q = 1) (hb : d310774 q = 1) : d310908 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d310908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42382, d310908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d310774 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42630 q = 1) (hb : d310774 q = 1) : d311102 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42630, d311102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42630, d311102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98643 (p : Pattern) (ha : d42636 p = 1) (hb : d310774 p = 1) : d311108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42627 q = 1) (hb : d310774 q = 1) : d311099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42627, d311099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98641 q ha hb
    | true =>
      simp only [d42627, d311099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98600 q ha hb
  have h2 (q : Pattern) (ha : d42628 q = 1) (hb : d310774 q = 1) : d311100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42628, d311100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42628, d311100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42629 q = 1) (hb : d310774 q = 1) : d311101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42629, d311101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42629, d311101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42631 q = 1) (hb : d310774 q = 1) : d311103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42631, d311103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98600 q ha hb
    | true =>
      simp only [d42631, d311103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98642 q ha hb
  have h5 (q : Pattern) (ha : d42632 q = 1) (hb : d310774 q = 1) : d311104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42632, d311104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42632, d311104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42633 q = 1) (hb : d310774 q = 1) : d311105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42633, d311105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42633, d311105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42634 q = 1) (hb : d310774 q = 1) : d311106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42634, d311106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42634, d311106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42384 q = 1) (hb : d310774 q = 1) : d310910 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98600 q ha hb
    | true =>
      simp only [d42384, d310910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
  have h9 (q : Pattern) (ha : d42385 q = 1) (hb : d310774 q = 1) : d310911 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d310911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42386 q = 1) (hb : d310774 q = 1) : d310912 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d310912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d310774 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d42262 q = 1) (hb : d310774 q = 1) : d310789 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98580 q ha hb
    | true =>
      simp only [d42262, d310789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42263 q = 1) (hb : d310774 q = 1) : d310790 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d310790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42264 q = 1) (hb : d310774 q = 1) : d310791 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d310791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42387 q = 1) (hb : d310774 q = 1) : d310913 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42387, d310913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42635 q = 1) (hb : d310774 q = 1) : d311107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42635, d311107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42635, d311107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42636 q = 1) (hb : d310774 q = 1) : d311108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42636, d311108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42636, d311108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro98644 (p : Pattern) (ha : d42642 p = 1) (hb : d310774 p = 1) : d311114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42637 q = 1) (hb : d310774 q = 1) : d311109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d311109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98643 q ha hb
    | true =>
      simp only [d42637, d311109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42638 q = 1) (hb : d310774 q = 1) : d311110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d311110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42638, d311110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42639 q = 1) (hb : d310774 q = 1) : d311111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d311111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d311111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42640 q = 1) (hb : d310774 q = 1) : d311112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d311112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d311112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42641 q = 1) (hb : d310774 q = 1) : d311113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d311113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d311113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42642 q = 1) (hb : d310774 q = 1) : d311114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42642, d311114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42642, d311114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98645 (p : Pattern) (ha : d42693 p = 1) (hb : d310774 p = 1) : d311120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42690 q = 1) (hb : d310774 q = 1) : d311117 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d311117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d311117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42691 q = 1) (hb : d310774 q = 1) : d311118 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d311118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d311118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42692 q = 1) (hb : d310774 q = 1) : d311119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d311119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d311119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42693 q = 1) (hb : d310774 q = 1) : d311120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42693, d311120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42693, d311120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98646 (p : Pattern) (ha : d309848 p = 1) (hb : d310774 p = 1) : d311126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42578 q = 1) (hb : d310774 q = 1) : d311054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d311054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98632 q ha hb
    | true =>
      simp only [d42578, d311054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98633 q ha hb
  have h2 (q : Pattern) (ha : d42579 q = 1) (hb : d310774 q = 1) : d311055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d311055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42579, d311055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42580 q = 1) (hb : d310774 q = 1) : d311056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d311056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d311056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42581 q = 1) (hb : d310774 q = 1) : d311057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d311057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42581, d311057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42588 q = 1) (hb : d310774 q = 1) : d311064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d311064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98634 q ha hb
    | true =>
      simp only [d42588, d311064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98635 q ha hb
  have h6 (q : Pattern) (ha : d42589 q = 1) (hb : d310774 q = 1) : d311065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d311065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42589, d311065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42590 q = 1) (hb : d310774 q = 1) : d311066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d311066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d311066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42643 q = 1) (hb : d310774 q = 1) : d311115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d311115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98644 q ha hb
    | true =>
      simp only [d42643, d311115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98620 q ha hb
  have h9 (q : Pattern) (ha : d309844 q = 1) (hb : d310774 q = 1) : d311116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d311116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d311116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42694 q = 1) (hb : d310774 q = 1) : d311121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d311121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98645 q ha hb
    | true =>
      simp only [d42694, d311121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42695 q = 1) (hb : d310774 q = 1) : d311122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d311122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d311122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d309845 q = 1) (hb : d310774 q = 1) : d311123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d311123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d311123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309846 q = 1) (hb : d310774 q = 1) : d311124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d311124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d311124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309847 q = 1) (hb : d310774 q = 1) : d311125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d311125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d311125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309848 q = 1) (hb : d310774 q = 1) : d311126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d311126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309848, d311126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98647 (p : Pattern) (ha : d42700 p = 1) (hb : d310774 p = 1) : d311127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d310774 q = 1) : d311024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d311024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42574 q = 1) (hb : d310774 q = 1) : d311050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d311050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42574, d311050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42700 q = 1) (hb : d310774 q = 1) : d311127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42700, d311127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42700, d311127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98648 (p : Pattern) (ha : d42701 p = 1) (hb : d310774 p = 1) : d311128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d310774 q = 1) : d311028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d311028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42576 q = 1) (hb : d310774 q = 1) : d311052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d311052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42576, d311052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42701 q = 1) (hb : d310774 q = 1) : d311128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42701, d311128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42701, d311128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98649 (p : Pattern) (ha : d42706 p = 1) (hb : d310774 p = 1) : d311133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d310774 q = 1) : d311023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d311023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42582 q = 1) (hb : d310774 q = 1) : d311058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d311058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42582, d311058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42583 q = 1) (hb : d310774 q = 1) : d311059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d311059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d311059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42706 q = 1) (hb : d310774 q = 1) : d311133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42706, d311133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42706, d311133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98650 (p : Pattern) (ha : d42707 p = 1) (hb : d310774 p = 1) : d311134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d310774 q = 1) : d311021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98619 q ha hb
    | true =>
      simp only [d42545, d311021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d310774 q = 1) : d311022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d311022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d310774 q = 1) : d311027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d311027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42585 q = 1) (hb : d310774 q = 1) : d311061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d311061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42585, d311061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42586 q = 1) (hb : d310774 q = 1) : d311062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d311062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d311062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42707 q = 1) (hb : d310774 q = 1) : d311134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42707, d311134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42707, d311134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98651 (p : Pattern) (ha : d42711 p = 1) (hb : d310774 p = 1) : d311138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42637 q = 1) (hb : d310774 q = 1) : d311109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d311109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98643 q ha hb
    | true =>
      simp only [d42637, d311109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42638 q = 1) (hb : d310774 q = 1) : d311110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d311110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42638, d311110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42639 q = 1) (hb : d310774 q = 1) : d311111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d311111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d311111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42640 q = 1) (hb : d310774 q = 1) : d311112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d311112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d311112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42641 q = 1) (hb : d310774 q = 1) : d311113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d311113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d311113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42711 q = 1) (hb : d310774 q = 1) : d311138 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42711, d311138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42711, d311138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98652 (p : Pattern) (ha : d42717 p = 1) (hb : d310774 p = 1) : d311141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d310774 q = 1) : d311017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98618 q ha hb
    | true =>
      simp only [d42541, d311017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d310774 q = 1) : d311018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d311018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42690 q = 1) (hb : d310774 q = 1) : d311117 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d311117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d311117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42691 q = 1) (hb : d310774 q = 1) : d311118 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d311118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d311118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42692 q = 1) (hb : d310774 q = 1) : d311119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d311119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d311119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42717 q = 1) (hb : d310774 q = 1) : d311141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42717, d311141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42717, d311141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98653 (p : Pattern) (ha : d309853 p = 1) (hb : d310774 p = 1) : d311147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42578 q = 1) (hb : d310774 q = 1) : d311054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d311054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98632 q ha hb
    | true =>
      simp only [d42578, d311054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98633 q ha hb
  have h2 (q : Pattern) (ha : d42579 q = 1) (hb : d310774 q = 1) : d311055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d311055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42579, d311055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42580 q = 1) (hb : d310774 q = 1) : d311056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d311056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d311056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42581 q = 1) (hb : d310774 q = 1) : d311057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d311057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42581, d311057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42588 q = 1) (hb : d310774 q = 1) : d311064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d311064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98634 q ha hb
    | true =>
      simp only [d42588, d311064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98635 q ha hb
  have h6 (q : Pattern) (ha : d42589 q = 1) (hb : d310774 q = 1) : d311065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d311065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42589, d311065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42590 q = 1) (hb : d310774 q = 1) : d311066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d311066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d311066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42643 q = 1) (hb : d310774 q = 1) : d311115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d311115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98644 q ha hb
    | true =>
      simp only [d42643, d311115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98620 q ha hb
  have h9 (q : Pattern) (ha : d309844 q = 1) (hb : d310774 q = 1) : d311116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d311116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d311116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42694 q = 1) (hb : d310774 q = 1) : d311121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d311121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98645 q ha hb
    | true =>
      simp only [d42694, d311121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42695 q = 1) (hb : d310774 q = 1) : d311122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d311122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d311122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d309845 q = 1) (hb : d310774 q = 1) : d311123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d311123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d311123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309846 q = 1) (hb : d310774 q = 1) : d311124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d311124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d311124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309847 q = 1) (hb : d310774 q = 1) : d311125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d311125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d311125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42702 q = 1) (hb : d310774 q = 1) : d311129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42702, d311129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98647 q ha hb
    | true =>
      simp only [d42702, d311129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98648 q ha hb
  have h16 (q : Pattern) (ha : d42703 q = 1) (hb : d310774 q = 1) : d311130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42703, d311130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42703, d311130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42704 q = 1) (hb : d310774 q = 1) : d311131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42704, d311131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42704, d311131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42705 q = 1) (hb : d310774 q = 1) : d311132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42705, d311132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42705, d311132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42708 q = 1) (hb : d310774 q = 1) : d311135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42708, d311135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98649 q ha hb
    | true =>
      simp only [d42708, d311135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98650 q ha hb
  have h20 (q : Pattern) (ha : d42709 q = 1) (hb : d310774 q = 1) : d311136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42709, d311136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42709, d311136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d42710 q = 1) (hb : d310774 q = 1) : d311137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42710, d311137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42710, d311137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42712 q = 1) (hb : d310774 q = 1) : d311139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d311139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98651 q ha hb
    | true =>
      simp only [d42712, d311139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98623 q ha hb
  have h23 (q : Pattern) (ha : d309849 q = 1) (hb : d310774 q = 1) : d311140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d311140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309849, d311140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d42718 q = 1) (hb : d310774 q = 1) : d311142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d311142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98652 q ha hb
    | true =>
      simp only [d42718, d311142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d42719 q = 1) (hb : d310774 q = 1) : d311143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d311143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42719, d311143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d309850 q = 1) (hb : d310774 q = 1) : d311144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d311144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309850, d311144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d309851 q = 1) (hb : d310774 q = 1) : d311145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d311145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309851, d311145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d309852 q = 1) (hb : d310774 q = 1) : d311146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d311146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309852, d311146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d309853 q = 1) (hb : d310774 q = 1) : d311147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d311147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309853, d311147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro98654 (p : Pattern) (ha : d309860 p = 1) (hb : d310774 p = 1) : d311167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42712 q = 1) (hb : d310774 q = 1) : d311139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d311139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98651 q ha hb
    | true =>
      simp only [d42712, d311139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98623 q ha hb
  have h2 (q : Pattern) (ha : d309849 q = 1) (hb : d310774 q = 1) : d311140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d311140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309849, d311140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42718 q = 1) (hb : d310774 q = 1) : d311142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d311142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98652 q ha hb
    | true =>
      simp only [d42718, d311142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42719 q = 1) (hb : d310774 q = 1) : d311143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d311143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42719, d311143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309850 q = 1) (hb : d310774 q = 1) : d311144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d311144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309850, d311144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309858 q = 1) (hb : d310774 q = 1) : d311165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d311165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309858, d311165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309859 q = 1) (hb : d310774 q = 1) : d311166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d311166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309859, d311166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309860 q = 1) (hb : d310774 q = 1) : d311167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d311167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309860, d311167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98655 (p : Pattern) (ha : d42765 p = 1) (hb : d310774 p = 1) : d311189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42751 q = 1) (hb : d310774 q = 1) : d311175 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d311175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42751, d311175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
  have h2 (q : Pattern) (ha : d42608 q = 1) (hb : d310774 q = 1) : d311080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
    | true =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42752 q = 1) (hb : d310774 q = 1) : d311176 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d311176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d311176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42609 q = 1) (hb : d310774 q = 1) : d311081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42753 q = 1) (hb : d310774 q = 1) : d311177 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d311177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d311177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42754 q = 1) (hb : d310774 q = 1) : d311178 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d311178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d311178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42755 q = 1) (hb : d310774 q = 1) : d311179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d311179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42755, d311179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
  have h8 (q : Pattern) (ha : d42613 q = 1) (hb : d310774 q = 1) : d311085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
    | true =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42756 q = 1) (hb : d310774 q = 1) : d311180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d311180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d311180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42614 q = 1) (hb : d310774 q = 1) : d311086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42757 q = 1) (hb : d310774 q = 1) : d311181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d311181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d311181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42758 q = 1) (hb : d310774 q = 1) : d311182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d311182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d311182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42759 q = 1) (hb : d310774 q = 1) : d311183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d311183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d311183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42760 q = 1) (hb : d310774 q = 1) : d311184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
  have h15 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42761 q = 1) (hb : d310774 q = 1) : d311185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42762 q = 1) (hb : d310774 q = 1) : d311186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42763 q = 1) (hb : d310774 q = 1) : d311187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42477 q = 1) (hb : d310774 q = 1) : d310972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
  have h21 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42478 q = 1) (hb : d310774 q = 1) : d310973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d42479 q = 1) (hb : d310774 q = 1) : d310974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42480 q = 1) (hb : d310774 q = 1) : d310975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d42764 q = 1) (hb : d310774 q = 1) : d311188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42764, d311188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42764, d311188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d42765 q = 1) (hb : d310774 q = 1) : d311189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42765, d311189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42765, d311189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro98656 (p : Pattern) (ha : d42769 p = 1) (hb : d310774 p = 1) : d311193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42477 q = 1) (hb : d310774 q = 1) : d310972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d310972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
  have h2 (q : Pattern) (ha : d42378 q = 1) (hb : d310774 q = 1) : d310904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98599 q ha hb
    | true =>
      simp only [d42378, d310904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42478 q = 1) (hb : d310774 q = 1) : d310973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42478, d310973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42379 q = 1) (hb : d310774 q = 1) : d310905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42379, d310905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42479 q = 1) (hb : d310774 q = 1) : d310974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42479, d310974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42480 q = 1) (hb : d310774 q = 1) : d310975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42480, d310975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d310774 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42481 q = 1) (hb : d310774 q = 1) : d310976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d310976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42481, d310976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d310774 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42769 q = 1) (hb : d310774 q = 1) : d311193 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42769, d311193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42769, d311193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro98657 (p : Pattern) (ha : d42775 p = 1) (hb : d310774 p = 1) : d311199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42766 q = 1) (hb : d310774 q = 1) : d311190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42766, d311190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98655 q ha hb
    | true =>
      simp only [d42766, d311190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98611 q ha hb
  have h2 (q : Pattern) (ha : d42767 q = 1) (hb : d310774 q = 1) : d311191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42767, d311191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42767, d311191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42768 q = 1) (hb : d310774 q = 1) : d311192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42768, d311192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42768, d311192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42770 q = 1) (hb : d310774 q = 1) : d311194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42770, d311194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98611 q ha hb
    | true =>
      simp only [d42770, d311194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98656 q ha hb
  have h5 (q : Pattern) (ha : d42771 q = 1) (hb : d310774 q = 1) : d311195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42771, d311195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42771, d311195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42772 q = 1) (hb : d310774 q = 1) : d311196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42772, d311196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42772, d311196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42773 q = 1) (hb : d310774 q = 1) : d311197 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42773, d311197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42773, d311197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42483 q = 1) (hb : d310774 q = 1) : d310978 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98611 q ha hb
    | true =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
  have h9 (q : Pattern) (ha : d42484 q = 1) (hb : d310774 q = 1) : d310979 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42485 q = 1) (hb : d310774 q = 1) : d310980 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d310774 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d42305 q = 1) (hb : d310774 q = 1) : d310832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
    | true =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42306 q = 1) (hb : d310774 q = 1) : d310833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42307 q = 1) (hb : d310774 q = 1) : d310834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42486 q = 1) (hb : d310774 q = 1) : d310981 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42774 q = 1) (hb : d310774 q = 1) : d311198 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42774, d311198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42774, d311198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42775 q = 1) (hb : d310774 q = 1) : d311199 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42775, d311199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42775, d311199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro98658 (p : Pattern) (ha : d42780 p = 1) (hb : d310774 p = 1) : d311204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42483 q = 1) (hb : d310774 q = 1) : d310978 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98611 q ha hb
    | true =>
      simp only [d42483, d310978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
  have h2 (q : Pattern) (ha : d42484 q = 1) (hb : d310774 q = 1) : d310979 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d310979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42485 q = 1) (hb : d310774 q = 1) : d310980 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d310980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d310774 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42305 q = 1) (hb : d310774 q = 1) : d310832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98587 q ha hb
    | true =>
      simp only [d42305, d310832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42306 q = 1) (hb : d310774 q = 1) : d310833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d310833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42307 q = 1) (hb : d310774 q = 1) : d310834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d310834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42486 q = 1) (hb : d310774 q = 1) : d310981 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d310981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42778 q = 1) (hb : d310774 q = 1) : d311202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d311202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42778, d311202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42779 q = 1) (hb : d310774 q = 1) : d311203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42779, d311203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42779, d311203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42780 q = 1) (hb : d310774 q = 1) : d311204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42780, d311204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42780, d311204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro98659 (p : Pattern) (ha : d42786 p = 1) (hb : d310774 p = 1) : d311210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42776 q = 1) (hb : d310774 q = 1) : d311200 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42776, d311200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98657 q ha hb
    | true =>
      simp only [d42776, d311200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42777 q = 1) (hb : d310774 q = 1) : d311201 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42777, d311201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42777, d311201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42781 q = 1) (hb : d310774 q = 1) : d311205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98658 q ha hb
    | true =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42782 q = 1) (hb : d310774 q = 1) : d311206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42783 q = 1) (hb : d310774 q = 1) : d311207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42783, d311207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42783, d311207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42784 q = 1) (hb : d310774 q = 1) : d311208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42784, d311208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42784, d311208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42785 q = 1) (hb : d310774 q = 1) : d311209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42785, d311209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42785, d311209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42786 q = 1) (hb : d310774 q = 1) : d311210 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42786, d311210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42786, d311210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98660 (p : Pattern) (ha : d42794 p = 1) (hb : d310774 p = 1) : d311218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42781 q = 1) (hb : d310774 q = 1) : d311205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98658 q ha hb
    | true =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42782 q = 1) (hb : d310774 q = 1) : d311206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42789 q = 1) (hb : d310774 q = 1) : d311213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d311213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98629 q ha hb
    | true =>
      simp only [d42789, d311213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42790 q = 1) (hb : d310774 q = 1) : d311214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d311214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42790, d311214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42791 q = 1) (hb : d310774 q = 1) : d311215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42791, d311215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42791, d311215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42792 q = 1) (hb : d310774 q = 1) : d311216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42792, d311216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42792, d311216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42793 q = 1) (hb : d310774 q = 1) : d311217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42793, d311217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42793, d311217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42794 q = 1) (hb : d310774 q = 1) : d311218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42794, d311218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42794, d311218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98661 (p : Pattern) (ha : d42833 p = 1) (hb : d310774 p = 1) : d311224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42781 q = 1) (hb : d310774 q = 1) : d311205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98658 q ha hb
    | true =>
      simp only [d42781, d311205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42782 q = 1) (hb : d310774 q = 1) : d311206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d311206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42830 q = 1) (hb : d310774 q = 1) : d311221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42830, d311221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42830, d311221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42831 q = 1) (hb : d310774 q = 1) : d311222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42831, d311222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42831, d311222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42832 q = 1) (hb : d310774 q = 1) : d311223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42832, d311223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42832, d311223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42833 q = 1) (hb : d310774 q = 1) : d311224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42833, d311224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42833, d311224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98662 (p : Pattern) (ha : d309870 p = 1) (hb : d310774 p = 1) : d311230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42795 q = 1) (hb : d310774 q = 1) : d311219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42795, d311219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98659 q ha hb
    | true =>
      simp only [d42795, d311219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98660 q ha hb
  have h2 (q : Pattern) (ha : d309866 q = 1) (hb : d310774 q = 1) : d311220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d311220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309866, d311220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42834 q = 1) (hb : d310774 q = 1) : d311225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42834, d311225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98661 q ha hb
    | true =>
      simp only [d42834, d311225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42835 q = 1) (hb : d310774 q = 1) : d311226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42835, d311226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42835, d311226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309867 q = 1) (hb : d310774 q = 1) : d311227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d311227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309867, d311227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309868 q = 1) (hb : d310774 q = 1) : d311228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d311228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309868, d311228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309869 q = 1) (hb : d310774 q = 1) : d311229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d311229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309869, d311229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309870 q = 1) (hb : d310774 q = 1) : d311230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d311230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309870, d311230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98663 (p : Pattern) (ha : d309876 p = 1) (hb : d310774 p = 1) : d311247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42561 q = 1) (hb : d310774 q = 1) : d311037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42561, d311037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42561, d311037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98622 q ha hb
  have h2 (q : Pattern) (ha : d42562 q = 1) (hb : d310774 q = 1) : d311038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42562, d311038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42562, d311038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42571 q = 1) (hb : d310774 q = 1) : d311047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98622 q ha hb
    | true =>
      simp only [d42571, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98625 q ha hb
  have h4 (q : Pattern) (ha : d42572 q = 1) (hb : d310774 q = 1) : d311048 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42572, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42573 q = 1) (hb : d310774 q = 1) : d311049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42573, d311049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42573, d311049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309854 q = 1) (hb : d310774 q = 1) : d311148 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d311148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98646 q ha hb
    | true =>
      simp only [d309854, d311148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98653 q ha hb
  have h7 (q : Pattern) (ha : d42737 q = 1) (hb : d310774 q = 1) : d311161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42737, d311161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98626 q ha hb
    | true =>
      simp only [d42737, d311161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98627 q ha hb
  have h8 (q : Pattern) (ha : d309855 q = 1) (hb : d310774 q = 1) : d311162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d311162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309855, d311162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309856 q = 1) (hb : d310774 q = 1) : d311163 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d311163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309856, d311163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d309857 q = 1) (hb : d310774 q = 1) : d311164 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d311164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309857, d311164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309861 q = 1) (hb : d310774 q = 1) : d311168 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d311168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309861, d311168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98654 q ha hb
  have h12 (q : Pattern) (ha : d42746 q = 1) (hb : d310774 q = 1) : d311170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42746, d311170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42746, d311170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98628 q ha hb
  have h13 (q : Pattern) (ha : d309862 q = 1) (hb : d310774 q = 1) : d311171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d311171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309862, d311171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309863 q = 1) (hb : d310774 q = 1) : d311172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d311172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309863, d311172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d309864 q = 1) (hb : d310774 q = 1) : d311173 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d311173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309864, d311173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d309865 q = 1) (hb : d310774 q = 1) : d311174 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d311174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309865, d311174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309871 q = 1) (hb : d310774 q = 1) : d311231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d311231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309871, d311231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98662 q ha hb
  have h18 (q : Pattern) (ha : d42851 q = 1) (hb : d310774 q = 1) : d311242 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42851, d311242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42851, d311242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98631 q ha hb
  have h19 (q : Pattern) (ha : d309872 q = 1) (hb : d310774 q = 1) : d311243 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d311243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309872, d311243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d309873 q = 1) (hb : d310774 q = 1) : d311244 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d311244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309873, d311244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d309874 q = 1) (hb : d310774 q = 1) : d311245 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d311245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309874, d311245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d309875 q = 1) (hb : d310774 q = 1) : d311246 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d311246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309875, d311246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d309876 q = 1) (hb : d310774 q = 1) : d311247 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d311247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309876, d311247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98664 (p : Pattern) (ha : d309882 p = 1) (hb : d310774 p = 1) : d311253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309877 q = 1) (hb : d310774 q = 1) : d311248 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d311248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309877, d311248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98663 q ha hb
  have h2 (q : Pattern) (ha : d309878 q = 1) (hb : d310774 q = 1) : d311249 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d311249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309878, d311249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309879 q = 1) (hb : d310774 q = 1) : d311250 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d311250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309879, d311250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309880 q = 1) (hb : d310774 q = 1) : d311251 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d311251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309880, d311251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309881 q = 1) (hb : d310774 q = 1) : d311252 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d311252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309881, d311252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309882 q = 1) (hb : d310774 q = 1) : d311253 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d311253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309882, d311253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98665 (p : Pattern) (ha : d42864 p = 1) (hb : d310774 p = 1) : d311255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d310774 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42253 q = 1) (hb : d310774 q = 1) : d310780 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d310780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42254 q = 1) (hb : d310774 q = 1) : d310781 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d310781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42864 q = 1) (hb : d310774 q = 1) : d311255 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42864, d311255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42864, d311255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98666 (p : Pattern) (ha : d42870 p = 1) (hb : d310774 p = 1) : d311261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42608 q = 1) (hb : d310774 q = 1) : d311080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
    | true =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42609 q = 1) (hb : d310774 q = 1) : d311081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42610 q = 1) (hb : d310774 q = 1) : d311082 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d311082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42610, d311082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42611 q = 1) (hb : d310774 q = 1) : d311083 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d311083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d311083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42613 q = 1) (hb : d310774 q = 1) : d311085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
    | true =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42614 q = 1) (hb : d310774 q = 1) : d311086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42615 q = 1) (hb : d310774 q = 1) : d311087 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d311087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42615, d311087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42616 q = 1) (hb : d310774 q = 1) : d311088 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d311088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d311088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42617 q = 1) (hb : d310774 q = 1) : d311089 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d311089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d311089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42623 q = 1) (hb : d310774 q = 1) : d311095 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42624 q = 1) (hb : d310774 q = 1) : d311096 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42867 q = 1) (hb : d310774 q = 1) : d311258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42868 q = 1) (hb : d310774 q = 1) : d311259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42869 q = 1) (hb : d310774 q = 1) : d311260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d311260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42869, d311260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42870 q = 1) (hb : d310774 q = 1) : d311261 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42870, d311261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42870, d311261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98667 (p : Pattern) (ha : d42873 p = 1) (hb : d310774 p = 1) : d311264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42370 q = 1) (hb : d310774 q = 1) : d310896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
    | true =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42371 q = 1) (hb : d310774 q = 1) : d310897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42372 q = 1) (hb : d310774 q = 1) : d310898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d310898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42372, d310898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42373 q = 1) (hb : d310774 q = 1) : d310899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d310899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d310899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42867 q = 1) (hb : d310774 q = 1) : d311258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42868 q = 1) (hb : d310774 q = 1) : d311259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42871 q = 1) (hb : d310774 q = 1) : d311262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42871, d311262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42871, d311262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42872 q = 1) (hb : d310774 q = 1) : d311263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42873 q = 1) (hb : d310774 q = 1) : d311264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42873, d311264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42873, d311264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98668 (p : Pattern) (ha : d42877 p = 1) (hb : d310774 p = 1) : d311268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42867 q = 1) (hb : d310774 q = 1) : d311258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42868 q = 1) (hb : d310774 q = 1) : d311259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42872 q = 1) (hb : d310774 q = 1) : d311263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42877 q = 1) (hb : d310774 q = 1) : d311268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42877, d311268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42877, d311268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98669 (p : Pattern) (ha : d42884 p = 1) (hb : d310774 p = 1) : d311275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42874 q = 1) (hb : d310774 q = 1) : d311265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d311265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98666 q ha hb
    | true =>
      simp only [d42874, d311265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98667 q ha hb
  have h2 (q : Pattern) (ha : d42875 q = 1) (hb : d310774 q = 1) : d311266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d311266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42875, d311266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42876 q = 1) (hb : d310774 q = 1) : d311267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d311267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42876, d311267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42878 q = 1) (hb : d310774 q = 1) : d311269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98667 q ha hb
    | true =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98668 q ha hb
  have h5 (q : Pattern) (ha : d42879 q = 1) (hb : d310774 q = 1) : d311270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42880 q = 1) (hb : d310774 q = 1) : d311271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42881 q = 1) (hb : d310774 q = 1) : d311272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d311272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42881, d311272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42882 q = 1) (hb : d310774 q = 1) : d311273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d311273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42882, d311273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42883 q = 1) (hb : d310774 q = 1) : d311274 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42883, d311274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42883, d311274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42884 q = 1) (hb : d310774 q = 1) : d311275 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42884, d311275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42884, d311275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro98670 (p : Pattern) (ha : d42888 p = 1) (hb : d310774 p = 1) : d311279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42878 q = 1) (hb : d310774 q = 1) : d311269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98667 q ha hb
    | true =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98668 q ha hb
  have h2 (q : Pattern) (ha : d42879 q = 1) (hb : d310774 q = 1) : d311270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42880 q = 1) (hb : d310774 q = 1) : d311271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42882 q = 1) (hb : d310774 q = 1) : d311273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d311273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42882, d311273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42887 q = 1) (hb : d310774 q = 1) : d311278 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42887, d311278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42887, d311278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42888 q = 1) (hb : d310774 q = 1) : d311279 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42888, d311279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42888, d311279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98671 (p : Pattern) (ha : d42894 p = 1) (hb : d310774 p = 1) : d311285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d310774 q = 1) : d311283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42893 q = 1) (hb : d310774 q = 1) : d311284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d311284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d311284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42894 q = 1) (hb : d310774 q = 1) : d311285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42894, d311285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42894, d311285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98672 (p : Pattern) (ha : d42898 p = 1) (hb : d310774 p = 1) : d311289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d310774 q = 1) : d311287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42897 q = 1) (hb : d310774 q = 1) : d311288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d311288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d311288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42898 q = 1) (hb : d310774 q = 1) : d311289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42898, d311289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42898, d311289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98673 (p : Pattern) (ha : d42904 p = 1) (hb : d310774 p = 1) : d311295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d310774 q = 1) : d311290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98671 q ha hb
    | true =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98672 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d310774 q = 1) : d311291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d310774 q = 1) : d311292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d310774 q = 1) : d311293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d310774 q = 1) : d311294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42904 q = 1) (hb : d310774 q = 1) : d311295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42904, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42904, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98674 (p : Pattern) (ha : d42907 p = 1) (hb : d310774 p = 1) : d311298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d310774 q = 1) : d311283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42893 q = 1) (hb : d310774 q = 1) : d311284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d311284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d311284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42907 q = 1) (hb : d310774 q = 1) : d311298 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42907, d311298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42907, d311298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98675 (p : Pattern) (ha : d42908 p = 1) (hb : d310774 p = 1) : d311299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d310774 q = 1) : d311287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42897 q = 1) (hb : d310774 q = 1) : d311288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d311288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d311288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42908 q = 1) (hb : d310774 q = 1) : d311299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42908, d311299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42908, d311299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98676 (p : Pattern) (ha : d42914 p = 1) (hb : d310774 p = 1) : d311305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d310774 q = 1) : d311290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98671 q ha hb
    | true =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98672 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d310774 q = 1) : d311291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d310774 q = 1) : d311292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d310774 q = 1) : d311293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d310774 q = 1) : d311294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42909 q = 1) (hb : d310774 q = 1) : d311300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98674 q ha hb
    | true =>
      simp only [d42909, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98675 q ha hb
  have h7 (q : Pattern) (ha : d42910 q = 1) (hb : d310774 q = 1) : d311301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42910, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42911 q = 1) (hb : d310774 q = 1) : d311302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42911, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42912 q = 1) (hb : d310774 q = 1) : d311303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42912, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42913 q = 1) (hb : d310774 q = 1) : d311304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42913, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42914 q = 1) (hb : d310774 q = 1) : d311305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42914, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42914, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98677 (p : Pattern) (ha : d43111 p = 1) (hb : d310774 p = 1) : d311418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d310774 q = 1) : d311290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98671 q ha hb
    | true =>
      simp only [d42899, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98672 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d310774 q = 1) : d311291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d310774 q = 1) : d311292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d310774 q = 1) : d311293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d310774 q = 1) : d311294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43106 q = 1) (hb : d310774 q = 1) : d311413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d311413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98672 q ha hb
    | true =>
      simp only [d43106, d311413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43107 q = 1) (hb : d310774 q = 1) : d311414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d311414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43107, d311414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43108 q = 1) (hb : d310774 q = 1) : d311415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d311415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43108, d311415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43109 q = 1) (hb : d310774 q = 1) : d311416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d311416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43109, d311416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43110 q = 1) (hb : d310774 q = 1) : d311417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d311417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43110, d311417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43111 q = 1) (hb : d310774 q = 1) : d311418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43111, d311418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43111, d311418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98678 (p : Pattern) (ha : d43117 p = 1) (hb : d310774 p = 1) : d311424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43106 q = 1) (hb : d310774 q = 1) : d311413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d311413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98672 q ha hb
    | true =>
      simp only [d43106, d311413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43107 q = 1) (hb : d310774 q = 1) : d311414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d311414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43107, d311414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43108 q = 1) (hb : d310774 q = 1) : d311415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d311415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43108, d311415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43109 q = 1) (hb : d310774 q = 1) : d311416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d311416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43109, d311416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43110 q = 1) (hb : d310774 q = 1) : d311417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d311417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43110, d311417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43112 q = 1) (hb : d310774 q = 1) : d311419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d311419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98675 q ha hb
    | true =>
      simp only [d43112, d311419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43113 q = 1) (hb : d310774 q = 1) : d311420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d311420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43113, d311420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43114 q = 1) (hb : d310774 q = 1) : d311421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d311421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43114, d311421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43115 q = 1) (hb : d310774 q = 1) : d311422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d311422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43115, d311422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43116 q = 1) (hb : d310774 q = 1) : d311423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d311423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43116, d311423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43117 q = 1) (hb : d310774 q = 1) : d311424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43117, d311424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43117, d311424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98679 (p : Pattern) (ha : d43126 p = 1) (hb : d310774 p = 1) : d311433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43112 q = 1) (hb : d310774 q = 1) : d311419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d311419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98675 q ha hb
    | true =>
      simp only [d43112, d311419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43113 q = 1) (hb : d310774 q = 1) : d311420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d311420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43113, d311420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43114 q = 1) (hb : d310774 q = 1) : d311421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d311421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43114, d311421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43115 q = 1) (hb : d310774 q = 1) : d311422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d311422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43115, d311422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43116 q = 1) (hb : d310774 q = 1) : d311423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d311423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43116, d311423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43126 q = 1) (hb : d310774 q = 1) : d311433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43126, d311433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43126, d311433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98680 (p : Pattern) (ha : d43163 p = 1) (hb : d310774 p = 1) : d311470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42472 q = 1) (hb : d310774 q = 1) : d310967 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d310967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42472, d310967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
  have h2 (q : Pattern) (ha : d42370 q = 1) (hb : d310774 q = 1) : d310896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98598 q ha hb
    | true =>
      simp only [d42370, d310896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42473 q = 1) (hb : d310774 q = 1) : d310968 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d310968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d310968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42371 q = 1) (hb : d310774 q = 1) : d310897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d310897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42474 q = 1) (hb : d310774 q = 1) : d310969 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d310969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d310969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42475 q = 1) (hb : d310774 q = 1) : d310970 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d310970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d310970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43147 q = 1) (hb : d310774 q = 1) : d311454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
  have h8 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43148 q = 1) (hb : d310774 q = 1) : d311455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43149 q = 1) (hb : d310774 q = 1) : d311456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43150 q = 1) (hb : d310774 q = 1) : d311457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43162 q = 1) (hb : d310774 q = 1) : d311469 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43162, d311469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43162, d311469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43156 q = 1) (hb : d310774 q = 1) : d311463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43163 q = 1) (hb : d310774 q = 1) : d311470 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43163, d311470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43163, d311470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98681 (p : Pattern) (ha : d43167 p = 1) (hb : d310774 p = 1) : d311474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43147 q = 1) (hb : d310774 q = 1) : d311454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
  have h2 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43148 q = 1) (hb : d310774 q = 1) : d311455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43149 q = 1) (hb : d310774 q = 1) : d311456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43150 q = 1) (hb : d310774 q = 1) : d311457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43156 q = 1) (hb : d310774 q = 1) : d311463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43167 q = 1) (hb : d310774 q = 1) : d311474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43167, d311474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43167, d311474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98682 (p : Pattern) (ha : d43186 p = 1) (hb : d310774 p = 1) : d311493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43168 q = 1) (hb : d310774 q = 1) : d311475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98680 q ha hb
    | true =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98681 q ha hb
  have h2 (q : Pattern) (ha : d43169 q = 1) (hb : d310774 q = 1) : d311476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43170 q = 1) (hb : d310774 q = 1) : d311477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43176 q = 1) (hb : d310774 q = 1) : d311483 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d311483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43176, d311483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43185 q = 1) (hb : d310774 q = 1) : d311492 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43185, d311492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43185, d311492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43186 q = 1) (hb : d310774 q = 1) : d311493 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43186, d311493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43186, d311493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98683 (p : Pattern) (ha : d43257 p = 1) (hb : d310774 p = 1) : d311516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43187 q = 1) (hb : d310774 q = 1) : d311494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d311494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98682 q ha hb
    | true =>
      simp only [d43187, d311494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43188 q = 1) (hb : d310774 q = 1) : d311495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d311495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43188, d311495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43254 q = 1) (hb : d310774 q = 1) : d311513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43254, d311513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43254, d311513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43255 q = 1) (hb : d310774 q = 1) : d311514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43255, d311514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43255, d311514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43256 q = 1) (hb : d310774 q = 1) : d311515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43256, d311515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43256, d311515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43257 q = 1) (hb : d310774 q = 1) : d311516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43257, d311516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43257, d311516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98684 (p : Pattern) (ha : d43263 p = 1) (hb : d310774 p = 1) : d311522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43258 q = 1) (hb : d310774 q = 1) : d311517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43258, d311517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98683 q ha hb
    | true =>
      simp only [d43258, d311517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43259 q = 1) (hb : d310774 q = 1) : d311518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43259, d311518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43259, d311518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43260 q = 1) (hb : d310774 q = 1) : d311519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43260, d311519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43260, d311519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43261 q = 1) (hb : d310774 q = 1) : d311520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43261, d311520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43261, d311520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43262 q = 1) (hb : d310774 q = 1) : d311521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43262, d311521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43262, d311521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43263 q = 1) (hb : d310774 q = 1) : d311522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43263, d311522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43263, d311522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98685 (p : Pattern) (ha : d42919 p = 1) (hb : d310774 p = 1) : d311310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d310774 q = 1) : d311283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42918 q = 1) (hb : d310774 q = 1) : d311309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d311309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42918, d311309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42919 q = 1) (hb : d310774 q = 1) : d311310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42919, d311310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42919, d311310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98686 (p : Pattern) (ha : d42921 p = 1) (hb : d310774 p = 1) : d311312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d310774 q = 1) : d311287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42920 q = 1) (hb : d310774 q = 1) : d311311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d311311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42920, d311311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42921 q = 1) (hb : d310774 q = 1) : d311312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42921, d311312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42921, d311312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98687 (p : Pattern) (ha : d42928 p = 1) (hb : d310774 p = 1) : d311319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42926 q = 1) (hb : d310774 q = 1) : d311317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d311317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42926, d311317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42927 q = 1) (hb : d310774 q = 1) : d311318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d311318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d311318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42928 q = 1) (hb : d310774 q = 1) : d311319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42928, d311319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42928, d311319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98688 (p : Pattern) (ha : d42931 p = 1) (hb : d310774 p = 1) : d311322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42929 q = 1) (hb : d310774 q = 1) : d311320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d311320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42929, d311320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42930 q = 1) (hb : d310774 q = 1) : d311321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d311321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d311321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42931 q = 1) (hb : d310774 q = 1) : d311322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42931, d311322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42931, d311322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98689 (p : Pattern) (ha : d42936 p = 1) (hb : d310774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42935 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42935, d310774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42935, d310774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d42936 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro98690 (p : Pattern) (ha : d42941 p = 1) (hb : d310774 p = 1) : d43867 p = 1 := by
  have h0 (q : Pattern) (ha : d2002 q = 1) (hb : d310774 q = 1) : d2002 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2005 q = 1) (hb : d271213 q = 1) : d2005 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1085 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42940 q = 1) (hb : d310774 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42940, d310774, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42940, d310774, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d42941 q = 1) (hb : d310774 q = 1) : d43867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42941, d43867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42941, d43867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro98691 (p : Pattern) (ha : d42945 p = 1) (hb : d310774 p = 1) : d311327 p = 1 := by
  have h0 (q : Pattern) (ha : d42592 q = 1) (hb : d271213 q = 1) : d42592 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42944 q = 1) (hb : d310774 q = 1) : d311067 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42944, d310774, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42944, d310774, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d42598 q = 1) (hb : d271213 q = 1) : d42598 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42600 q = 1) (hb : d310774 q = 1) : d311072 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d310774, d311072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42600, d310774, d311072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42945 q = 1) (hb : d310774 q = 1) : d311327 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42945, d311327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42945, d311327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98692 (p : Pattern) (ha : d42954 p = 1) (hb : d310774 p = 1) : d311336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98689 q ha hb
    | true =>
      simp only [d42937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42595 q = 1) (hb : d310774 q = 1) : d311069 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42596 q = 1) (hb : d310774 q = 1) : d311070 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42939 q = 1) (hb : d310774 q = 1) : d311326 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42939, d311326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42939, d311326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42942 q = 1) (hb : d310774 q = 1) : d43868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98690 q ha hb
    | true =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42943 q = 1) (hb : d310774 q = 1) : d43869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42946 q = 1) (hb : d310774 q = 1) : d311328 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d311328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98691 q ha hb
    | true =>
      simp only [d42946, d311328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42947 q = 1) (hb : d310774 q = 1) : d311329 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d311329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42947, d311329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42948 q = 1) (hb : d310774 q = 1) : d311330 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d311330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42948, d311330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42949 q = 1) (hb : d310774 q = 1) : d311331 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42949, d311331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42949, d311331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42950 q = 1) (hb : d310774 q = 1) : d311332 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42950, d311332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42950, d311332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42597 q = 1) (hb : d310774 q = 1) : d311071 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42951 q = 1) (hb : d310774 q = 1) : d311333 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d311333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42951, d311333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42952 q = 1) (hb : d310774 q = 1) : d311334 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42952, d311334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42952, d311334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d42953 q = 1) (hb : d310774 q = 1) : d311335 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42953, d311335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42953, d311335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d42954 q = 1) (hb : d310774 q = 1) : d311336 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42954, d311336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42954, d311336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98693 (p : Pattern) (ha : d42961 p = 1) (hb : d310774 p = 1) : d311341 p = 1 := by
  have h0 (q : Pattern) (ha : d42361 q = 1) (hb : d271213 q = 1) : d42361 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42959 q = 1) (hb : d310774 q = 1) : d310888 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42959, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42959, d310774, d310888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1540 q = 1) (hb : d271213 q = 1) : d1540 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42960 q = 1) (hb : d310774 q = 1) : d1541 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42960, d310774, d1541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42960, d310774, d1541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42961 q = 1) (hb : d310774 q = 1) : d311341 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42961, d311341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42961, d311341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98694 (p : Pattern) (ha : d42967 p = 1) (hb : d310774 p = 1) : d311347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d310774 q = 1) : d311069 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d310774 q = 1) : d311070 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42364 q = 1) (hb : d310774 q = 1) : d310890 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d42364, d310890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42365 q = 1) (hb : d310774 q = 1) : d310891 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d310891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42597 q = 1) (hb : d310774 q = 1) : d311071 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d311071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d310774 q = 1) : d311074 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98637 q ha hb
    | true =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d310774 q = 1) : d311075 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d310774 q = 1) : d311076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42605 q = 1) (hb : d310774 q = 1) : d311077 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d311077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d311077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42606 q = 1) (hb : d310774 q = 1) : d311078 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d311078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d311078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42962 q = 1) (hb : d310774 q = 1) : d311342 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98693 q ha hb
    | true =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42963 q = 1) (hb : d310774 q = 1) : d311343 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42964 q = 1) (hb : d310774 q = 1) : d311344 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d311344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42964, d311344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d42965 q = 1) (hb : d310774 q = 1) : d311345 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d311345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42965, d311345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d42966 q = 1) (hb : d310774 q = 1) : d311346 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d311346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42966, d311346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42967 q = 1) (hb : d310774 q = 1) : d311347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42967, d311347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42967, d311347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro98695 (p : Pattern) (ha : d42976 p = 1) (hb : d310774 p = 1) : d311356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d310774 q = 1) : d311069 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d42595, d311069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d310774 q = 1) : d311070 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d311070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42962 q = 1) (hb : d310774 q = 1) : d311342 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98693 q ha hb
    | true =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42963 q = 1) (hb : d310774 q = 1) : d311343 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42973 q = 1) (hb : d310774 q = 1) : d311353 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42973, d311353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42973, d311353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42974 q = 1) (hb : d310774 q = 1) : d311354 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42974, d311354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42974, d311354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42975 q = 1) (hb : d310774 q = 1) : d311355 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42975, d311355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42975, d311355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42964 q = 1) (hb : d310774 q = 1) : d311344 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d311344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42964, d311344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42965 q = 1) (hb : d310774 q = 1) : d311345 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d311345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42965, d311345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42966 q = 1) (hb : d310774 q = 1) : d311346 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d311346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42966, d311346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42976 q = 1) (hb : d310774 q = 1) : d311356 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42976, d311356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42976, d311356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro98696 (p : Pattern) (ha : d42982 p = 1) (hb : d310774 p = 1) : d311362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42955 q = 1) (hb : d310774 q = 1) : d311337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d311337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98692 q ha hb
    | true =>
      simp only [d42955, d311337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42956 q = 1) (hb : d310774 q = 1) : d311338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d311338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42956, d311338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42957 q = 1) (hb : d310774 q = 1) : d311339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42957, d311339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42957, d311339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42958 q = 1) (hb : d310774 q = 1) : d311340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42958, d311340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42958, d311340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42968 q = 1) (hb : d310774 q = 1) : d311348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d311348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98694 q ha hb
    | true =>
      simp only [d42968, d311348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42969 q = 1) (hb : d310774 q = 1) : d311349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d311349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42969, d311349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42970 q = 1) (hb : d310774 q = 1) : d311350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42970, d311350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42970, d311350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42971 q = 1) (hb : d310774 q = 1) : d311351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42971, d311351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42971, d311351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42972 q = 1) (hb : d310774 q = 1) : d311352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42972, d311352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42972, d311352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42977 q = 1) (hb : d310774 q = 1) : d311357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d311357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98695 q ha hb
    | true =>
      simp only [d42977, d311357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42978 q = 1) (hb : d310774 q = 1) : d311358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d311358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42978, d311358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42979 q = 1) (hb : d310774 q = 1) : d311359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42979, d311359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42979, d311359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42980 q = 1) (hb : d310774 q = 1) : d311360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42980, d311360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42980, d311360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42623 q = 1) (hb : d310774 q = 1) : d311095 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42624 q = 1) (hb : d310774 q = 1) : d311096 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42981 q = 1) (hb : d310774 q = 1) : d311361 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42981, d311361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42981, d311361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42982 q = 1) (hb : d310774 q = 1) : d311362 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42982, d311362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42982, d311362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98697 (p : Pattern) (ha : d42986 p = 1) (hb : d310774 p = 1) : d311366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42623 q = 1) (hb : d310774 q = 1) : d311095 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d311095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42624 q = 1) (hb : d310774 q = 1) : d311096 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42624, d311096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42867 q = 1) (hb : d310774 q = 1) : d311258 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d311258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42868 q = 1) (hb : d310774 q = 1) : d311259 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d311259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42869 q = 1) (hb : d310774 q = 1) : d311260 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d311260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42869, d311260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42872 q = 1) (hb : d310774 q = 1) : d311263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d311263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42986 q = 1) (hb : d310774 q = 1) : d311366 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42986, d311366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42986, d311366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98698 (p : Pattern) (ha : d42992 p = 1) (hb : d310774 p = 1) : d311372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42983 q = 1) (hb : d310774 q = 1) : d311363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42983, d311363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98696 q ha hb
    | true =>
      simp only [d42983, d311363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98666 q ha hb
  have h2 (q : Pattern) (ha : d42984 q = 1) (hb : d310774 q = 1) : d311364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42984, d311364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42984, d311364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42985 q = 1) (hb : d310774 q = 1) : d311365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42985, d311365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42985, d311365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42987 q = 1) (hb : d310774 q = 1) : d311367 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42987, d311367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98666 q ha hb
    | true =>
      simp only [d42987, d311367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98697 q ha hb
  have h5 (q : Pattern) (ha : d42988 q = 1) (hb : d310774 q = 1) : d311368 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42988, d311368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42988, d311368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42989 q = 1) (hb : d310774 q = 1) : d311369 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42989, d311369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42989, d311369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42990 q = 1) (hb : d310774 q = 1) : d311370 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42990, d311370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42990, d311370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42874 q = 1) (hb : d310774 q = 1) : d311265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d311265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98666 q ha hb
    | true =>
      simp only [d42874, d311265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98667 q ha hb
  have h9 (q : Pattern) (ha : d42875 q = 1) (hb : d310774 q = 1) : d311266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d311266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42875, d311266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42876 q = 1) (hb : d310774 q = 1) : d311267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d311267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42876, d311267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42878 q = 1) (hb : d310774 q = 1) : d311269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98667 q ha hb
    | true =>
      simp only [d42878, d311269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98668 q ha hb
  have h12 (q : Pattern) (ha : d42879 q = 1) (hb : d310774 q = 1) : d311270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d311270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42880 q = 1) (hb : d310774 q = 1) : d311271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d311271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42881 q = 1) (hb : d310774 q = 1) : d311272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d311272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42881, d311272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42991 q = 1) (hb : d310774 q = 1) : d311371 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42991, d311371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42991, d311371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42992 q = 1) (hb : d310774 q = 1) : d311372 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42992, d311372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42992, d311372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro98699 (p : Pattern) (ha : d42998 p = 1) (hb : d310774 p = 1) : d311378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42993 q = 1) (hb : d310774 q = 1) : d311373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d311373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98698 q ha hb
    | true =>
      simp only [d42993, d311373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42994 q = 1) (hb : d310774 q = 1) : d311374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d311374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42994, d311374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42995 q = 1) (hb : d310774 q = 1) : d311375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d311375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d311375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42996 q = 1) (hb : d310774 q = 1) : d311376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d311376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d311376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42997 q = 1) (hb : d310774 q = 1) : d311377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d311377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d311377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42998 q = 1) (hb : d310774 q = 1) : d311378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42998, d311378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42998, d311378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98700 (p : Pattern) (ha : d43074 p = 1) (hb : d310774 p = 1) : d311384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43071 q = 1) (hb : d310774 q = 1) : d311381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d311381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d311381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43072 q = 1) (hb : d310774 q = 1) : d311382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d311382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d311382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43073 q = 1) (hb : d310774 q = 1) : d311383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d311383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d311383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43074 q = 1) (hb : d310774 q = 1) : d311384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43074, d311384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43074, d311384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98701 (p : Pattern) (ha : d309888 p = 1) (hb : d310774 p = 1) : d311390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42922 q = 1) (hb : d310774 q = 1) : d311313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d311313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98685 q ha hb
    | true =>
      simp only [d42922, d311313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98686 q ha hb
  have h2 (q : Pattern) (ha : d42923 q = 1) (hb : d310774 q = 1) : d311314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d311314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42923, d311314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42924 q = 1) (hb : d310774 q = 1) : d311315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d311315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d311315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42925 q = 1) (hb : d310774 q = 1) : d311316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d311316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42925, d311316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42932 q = 1) (hb : d310774 q = 1) : d311323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d311323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98687 q ha hb
    | true =>
      simp only [d42932, d311323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98688 q ha hb
  have h6 (q : Pattern) (ha : d42933 q = 1) (hb : d310774 q = 1) : d311324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d311324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42933, d311324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42934 q = 1) (hb : d310774 q = 1) : d311325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d311325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d311325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42999 q = 1) (hb : d310774 q = 1) : d311379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d311379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98699 q ha hb
    | true =>
      simp only [d42999, d311379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98671 q ha hb
  have h9 (q : Pattern) (ha : d309884 q = 1) (hb : d310774 q = 1) : d311380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d311380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309884, d311380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43075 q = 1) (hb : d310774 q = 1) : d311385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d311385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98700 q ha hb
    | true =>
      simp only [d43075, d311385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43076 q = 1) (hb : d310774 q = 1) : d311386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d311386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d311386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d309885 q = 1) (hb : d310774 q = 1) : d311387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d311387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d311387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309886 q = 1) (hb : d310774 q = 1) : d311388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d311388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309886, d311388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309887 q = 1) (hb : d310774 q = 1) : d311389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d311389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309887, d311389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309888 q = 1) (hb : d310774 q = 1) : d311390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d311390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309888, d311390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98702 (p : Pattern) (ha : d43081 p = 1) (hb : d310774 p = 1) : d311391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d310774 q = 1) : d311283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d311283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42918 q = 1) (hb : d310774 q = 1) : d311309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d311309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42918, d311309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43081 q = 1) (hb : d310774 q = 1) : d311391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43081, d311391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43081, d311391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98703 (p : Pattern) (ha : d43082 p = 1) (hb : d310774 p = 1) : d311392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d310774 q = 1) : d311287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d311287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42920 q = 1) (hb : d310774 q = 1) : d311311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d311311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42920, d311311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43082 q = 1) (hb : d310774 q = 1) : d311392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43082, d311392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43082, d311392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98704 (p : Pattern) (ha : d43087 p = 1) (hb : d310774 p = 1) : d311397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d310774 q = 1) : d311282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d311282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42926 q = 1) (hb : d310774 q = 1) : d311317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d311317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42926, d311317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42927 q = 1) (hb : d310774 q = 1) : d311318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d311318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d311318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43087 q = 1) (hb : d310774 q = 1) : d311397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43087, d311397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43087, d311397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98705 (p : Pattern) (ha : d43088 p = 1) (hb : d310774 p = 1) : d311398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d310774 q = 1) : d311280 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98670 q ha hb
    | true =>
      simp only [d42889, d311280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d310774 q = 1) : d311281 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d311281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d310774 q = 1) : d311286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d311286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42929 q = 1) (hb : d310774 q = 1) : d311320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d311320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42929, d311320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42930 q = 1) (hb : d310774 q = 1) : d311321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d311321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d311321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43088 q = 1) (hb : d310774 q = 1) : d311398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43088, d311398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43088, d311398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98706 (p : Pattern) (ha : d43092 p = 1) (hb : d310774 p = 1) : d311402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42993 q = 1) (hb : d310774 q = 1) : d311373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d311373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98698 q ha hb
    | true =>
      simp only [d42993, d311373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42994 q = 1) (hb : d310774 q = 1) : d311374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d311374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42994, d311374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42995 q = 1) (hb : d310774 q = 1) : d311375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d311375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d311375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42996 q = 1) (hb : d310774 q = 1) : d311376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d311376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d311376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42997 q = 1) (hb : d310774 q = 1) : d311377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d311377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d311377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43092 q = 1) (hb : d310774 q = 1) : d311402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43092, d311402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43092, d311402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98707 (p : Pattern) (ha : d43098 p = 1) (hb : d310774 p = 1) : d311405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d310774 q = 1) : d311276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98669 q ha hb
    | true =>
      simp only [d42885, d311276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d310774 q = 1) : d311277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d311277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43071 q = 1) (hb : d310774 q = 1) : d311381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d311381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d311381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43072 q = 1) (hb : d310774 q = 1) : d311382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d311382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d311382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43073 q = 1) (hb : d310774 q = 1) : d311383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d311383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d311383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43098 q = 1) (hb : d310774 q = 1) : d311405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43098, d311405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43098, d311405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98708 (p : Pattern) (ha : d309893 p = 1) (hb : d310774 p = 1) : d311411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42922 q = 1) (hb : d310774 q = 1) : d311313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d311313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98685 q ha hb
    | true =>
      simp only [d42922, d311313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98686 q ha hb
  have h2 (q : Pattern) (ha : d42923 q = 1) (hb : d310774 q = 1) : d311314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d311314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42923, d311314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42924 q = 1) (hb : d310774 q = 1) : d311315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d311315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d311315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42925 q = 1) (hb : d310774 q = 1) : d311316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d311316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42925, d311316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42932 q = 1) (hb : d310774 q = 1) : d311323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d311323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98687 q ha hb
    | true =>
      simp only [d42932, d311323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98688 q ha hb
  have h6 (q : Pattern) (ha : d42933 q = 1) (hb : d310774 q = 1) : d311324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d311324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42933, d311324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42934 q = 1) (hb : d310774 q = 1) : d311325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d311325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d311325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42999 q = 1) (hb : d310774 q = 1) : d311379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d311379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98699 q ha hb
    | true =>
      simp only [d42999, d311379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98671 q ha hb
  have h9 (q : Pattern) (ha : d309884 q = 1) (hb : d310774 q = 1) : d311380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d311380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309884, d311380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43075 q = 1) (hb : d310774 q = 1) : d311385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d311385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98700 q ha hb
    | true =>
      simp only [d43075, d311385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43076 q = 1) (hb : d310774 q = 1) : d311386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d311386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d311386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d309885 q = 1) (hb : d310774 q = 1) : d311387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d311387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d311387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309886 q = 1) (hb : d310774 q = 1) : d311388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d311388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309886, d311388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309887 q = 1) (hb : d310774 q = 1) : d311389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d311389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309887, d311389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43083 q = 1) (hb : d310774 q = 1) : d311393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43083, d311393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98702 q ha hb
    | true =>
      simp only [d43083, d311393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98703 q ha hb
  have h16 (q : Pattern) (ha : d43084 q = 1) (hb : d310774 q = 1) : d311394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43084, d311394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43084, d311394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43085 q = 1) (hb : d310774 q = 1) : d311395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43085, d311395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43085, d311395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43086 q = 1) (hb : d310774 q = 1) : d311396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43086, d311396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43086, d311396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43089 q = 1) (hb : d310774 q = 1) : d311399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43089, d311399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98704 q ha hb
    | true =>
      simp only [d43089, d311399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98705 q ha hb
  have h20 (q : Pattern) (ha : d43090 q = 1) (hb : d310774 q = 1) : d311400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43090, d311400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43090, d311400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d43091 q = 1) (hb : d310774 q = 1) : d311401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43091, d311401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43091, d311401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d43093 q = 1) (hb : d310774 q = 1) : d311403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d311403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98706 q ha hb
    | true =>
      simp only [d43093, d311403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98674 q ha hb
  have h23 (q : Pattern) (ha : d309889 q = 1) (hb : d310774 q = 1) : d311404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d311404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309889, d311404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d43099 q = 1) (hb : d310774 q = 1) : d311406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d311406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98707 q ha hb
    | true =>
      simp only [d43099, d311406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d43100 q = 1) (hb : d310774 q = 1) : d311407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d311407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43100, d311407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d309890 q = 1) (hb : d310774 q = 1) : d311408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d311408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309890, d311408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d309891 q = 1) (hb : d310774 q = 1) : d311409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d311409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309891, d311409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d309892 q = 1) (hb : d310774 q = 1) : d311410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d311410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309892, d311410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d309893 q = 1) (hb : d310774 q = 1) : d311411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d311411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309893, d311411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro98709 (p : Pattern) (ha : d309900 p = 1) (hb : d310774 p = 1) : d311431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43093 q = 1) (hb : d310774 q = 1) : d311403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d311403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98706 q ha hb
    | true =>
      simp only [d43093, d311403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98674 q ha hb
  have h2 (q : Pattern) (ha : d309889 q = 1) (hb : d310774 q = 1) : d311404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d311404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309889, d311404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43099 q = 1) (hb : d310774 q = 1) : d311406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d311406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98707 q ha hb
    | true =>
      simp only [d43099, d311406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43100 q = 1) (hb : d310774 q = 1) : d311407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d311407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43100, d311407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309890 q = 1) (hb : d310774 q = 1) : d311408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d311408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309890, d311408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309898 q = 1) (hb : d310774 q = 1) : d311429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d311429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309898, d311429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309899 q = 1) (hb : d310774 q = 1) : d311430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d311430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309899, d311430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309900 q = 1) (hb : d310774 q = 1) : d311431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d311431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309900, d311431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98710 (p : Pattern) (ha : d43146 p = 1) (hb : d310774 p = 1) : d311453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43132 q = 1) (hb : d310774 q = 1) : d311439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43132, d311439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43132, d311439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98692 q ha hb
  have h2 (q : Pattern) (ha : d42955 q = 1) (hb : d310774 q = 1) : d311337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d311337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98692 q ha hb
    | true =>
      simp only [d42955, d311337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43133 q = 1) (hb : d310774 q = 1) : d311440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43133, d311440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43133, d311440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42956 q = 1) (hb : d310774 q = 1) : d311338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d311338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42956, d311338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43134 q = 1) (hb : d310774 q = 1) : d311441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43134, d311441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43134, d311441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43135 q = 1) (hb : d310774 q = 1) : d311442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43135, d311442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43135, d311442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43136 q = 1) (hb : d310774 q = 1) : d311443 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43136, d311443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43136, d311443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98694 q ha hb
  have h8 (q : Pattern) (ha : d42968 q = 1) (hb : d310774 q = 1) : d311348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d311348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98694 q ha hb
    | true =>
      simp only [d42968, d311348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43137 q = 1) (hb : d310774 q = 1) : d311444 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43137, d311444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43137, d311444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42969 q = 1) (hb : d310774 q = 1) : d311349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d311349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42969, d311349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43138 q = 1) (hb : d310774 q = 1) : d311445 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43138, d311445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43138, d311445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43139 q = 1) (hb : d310774 q = 1) : d311446 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43139, d311446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43139, d311446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43140 q = 1) (hb : d310774 q = 1) : d311447 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43140, d311447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43140, d311447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43141 q = 1) (hb : d310774 q = 1) : d311448 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43141, d311448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43141, d311448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98695 q ha hb
  have h15 (q : Pattern) (ha : d42977 q = 1) (hb : d310774 q = 1) : d311357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d311357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98695 q ha hb
    | true =>
      simp only [d42977, d311357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43142 q = 1) (hb : d310774 q = 1) : d311449 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43142, d311449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43142, d311449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42978 q = 1) (hb : d310774 q = 1) : d311358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d311358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42978, d311358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43143 q = 1) (hb : d310774 q = 1) : d311450 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43143, d311450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43143, d311450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43144 q = 1) (hb : d310774 q = 1) : d311451 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43144, d311451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43144, d311451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42760 q = 1) (hb : d310774 q = 1) : d311184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
  have h21 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42761 q = 1) (hb : d310774 q = 1) : d311185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d42762 q = 1) (hb : d310774 q = 1) : d311186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42763 q = 1) (hb : d310774 q = 1) : d311187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d43145 q = 1) (hb : d310774 q = 1) : d311452 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43145, d311452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43145, d311452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d43146 q = 1) (hb : d310774 q = 1) : d311453 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43146, d311453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43146, d311453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro98711 (p : Pattern) (ha : d43152 p = 1) (hb : d310774 p = 1) : d311459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42751 q = 1) (hb : d310774 q = 1) : d311175 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d311175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42751, d311175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
  have h2 (q : Pattern) (ha : d42608 q = 1) (hb : d310774 q = 1) : d311080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98638 q ha hb
    | true =>
      simp only [d42608, d311080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42752 q = 1) (hb : d310774 q = 1) : d311176 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d311176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d311176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42609 q = 1) (hb : d310774 q = 1) : d311081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d311081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42753 q = 1) (hb : d310774 q = 1) : d311177 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d311177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d311177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42754 q = 1) (hb : d310774 q = 1) : d311178 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d311178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d311178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42755 q = 1) (hb : d310774 q = 1) : d311179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d311179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42755, d311179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
  have h8 (q : Pattern) (ha : d42613 q = 1) (hb : d310774 q = 1) : d311085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98639 q ha hb
    | true =>
      simp only [d42613, d311085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42756 q = 1) (hb : d310774 q = 1) : d311180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d311180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d311180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42614 q = 1) (hb : d310774 q = 1) : d311086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d311086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42757 q = 1) (hb : d310774 q = 1) : d311181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d311181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d311181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42758 q = 1) (hb : d310774 q = 1) : d311182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d311182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d311182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42759 q = 1) (hb : d310774 q = 1) : d311183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d311183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d311183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42760 q = 1) (hb : d310774 q = 1) : d311184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
  have h15 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42761 q = 1) (hb : d310774 q = 1) : d311185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42762 q = 1) (hb : d310774 q = 1) : d311186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42763 q = 1) (hb : d310774 q = 1) : d311187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d43147 q = 1) (hb : d310774 q = 1) : d311454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
  have h21 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d43148 q = 1) (hb : d310774 q = 1) : d311455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d43149 q = 1) (hb : d310774 q = 1) : d311456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d43150 q = 1) (hb : d310774 q = 1) : d311457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d43151 q = 1) (hb : d310774 q = 1) : d311458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d311458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43151, d311458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d43152 q = 1) (hb : d310774 q = 1) : d311459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43152, d311459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43152, d311459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro98712 (p : Pattern) (ha : d43157 p = 1) (hb : d310774 p = 1) : d311464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42760 q = 1) (hb : d310774 q = 1) : d311184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d311184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
  have h2 (q : Pattern) (ha : d42621 q = 1) (hb : d310774 q = 1) : d311093 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98640 q ha hb
    | true =>
      simp only [d42621, d311093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42761 q = 1) (hb : d310774 q = 1) : d311185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42761, d311185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42622 q = 1) (hb : d310774 q = 1) : d311094 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42622, d311094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42762 q = 1) (hb : d310774 q = 1) : d311186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42762, d311186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42763 q = 1) (hb : d310774 q = 1) : d311187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42763, d311187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43147 q = 1) (hb : d310774 q = 1) : d311454 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d311454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
  have h8 (q : Pattern) (ha : d42865 q = 1) (hb : d310774 q = 1) : d311256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98665 q ha hb
    | true =>
      simp only [d42865, d311256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43148 q = 1) (hb : d310774 q = 1) : d311455 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d311455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42866 q = 1) (hb : d310774 q = 1) : d311257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d311257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43149 q = 1) (hb : d310774 q = 1) : d311456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d311456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43150 q = 1) (hb : d310774 q = 1) : d311457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d311457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43151 q = 1) (hb : d310774 q = 1) : d311458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d311458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43151, d311458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43156 q = 1) (hb : d310774 q = 1) : d311463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d311463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43157 q = 1) (hb : d310774 q = 1) : d311464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43157, d311464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43157, d311464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98713 (p : Pattern) (ha : d43173 p = 1) (hb : d310774 p = 1) : d311480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43153 q = 1) (hb : d310774 q = 1) : d311460 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43153, d311460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98710 q ha hb
    | true =>
      simp only [d43153, d311460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98711 q ha hb
  have h2 (q : Pattern) (ha : d43154 q = 1) (hb : d310774 q = 1) : d311461 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43154, d311461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43154, d311461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43155 q = 1) (hb : d310774 q = 1) : d311462 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43155, d311462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43155, d311462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43158 q = 1) (hb : d310774 q = 1) : d311465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43158, d311465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98711 q ha hb
    | true =>
      simp only [d43158, d311465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98712 q ha hb
  have h5 (q : Pattern) (ha : d43159 q = 1) (hb : d310774 q = 1) : d311466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43159, d311466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43159, d311466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43160 q = 1) (hb : d310774 q = 1) : d311467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43160, d311467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43160, d311467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43161 q = 1) (hb : d310774 q = 1) : d311468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43161, d311468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43161, d311468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43164 q = 1) (hb : d310774 q = 1) : d311471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d311471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98711 q ha hb
    | true =>
      simp only [d43164, d311471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98680 q ha hb
  have h9 (q : Pattern) (ha : d43165 q = 1) (hb : d310774 q = 1) : d311472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d311472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43165, d311472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43166 q = 1) (hb : d310774 q = 1) : d311473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d311473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43166, d311473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43168 q = 1) (hb : d310774 q = 1) : d311475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98680 q ha hb
    | true =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98681 q ha hb
  have h12 (q : Pattern) (ha : d43169 q = 1) (hb : d310774 q = 1) : d311476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43170 q = 1) (hb : d310774 q = 1) : d311477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43171 q = 1) (hb : d310774 q = 1) : d311478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d311478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43171, d311478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43172 q = 1) (hb : d310774 q = 1) : d311479 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43172, d311479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43172, d311479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d43173 q = 1) (hb : d310774 q = 1) : d311480 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43173, d311480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43173, d311480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro98714 (p : Pattern) (ha : d43178 p = 1) (hb : d310774 p = 1) : d311485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43164 q = 1) (hb : d310774 q = 1) : d311471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d311471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98711 q ha hb
    | true =>
      simp only [d43164, d311471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98680 q ha hb
  have h2 (q : Pattern) (ha : d43165 q = 1) (hb : d310774 q = 1) : d311472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d311472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43165, d311472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43166 q = 1) (hb : d310774 q = 1) : d311473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d311473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43166, d311473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43168 q = 1) (hb : d310774 q = 1) : d311475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98680 q ha hb
    | true =>
      simp only [d43168, d311475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98681 q ha hb
  have h5 (q : Pattern) (ha : d43169 q = 1) (hb : d310774 q = 1) : d311476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d311476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43170 q = 1) (hb : d310774 q = 1) : d311477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d311477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43171 q = 1) (hb : d310774 q = 1) : d311478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d311478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43171, d311478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43176 q = 1) (hb : d310774 q = 1) : d311483 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d311483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43176, d311483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43177 q = 1) (hb : d310774 q = 1) : d311484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43177, d311484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43177, d311484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43178 q = 1) (hb : d310774 q = 1) : d311485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43178, d311485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43178, d311485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro98715 (p : Pattern) (ha : d43184 p = 1) (hb : d310774 p = 1) : d311491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43174 q = 1) (hb : d310774 q = 1) : d311481 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43174, d311481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98713 q ha hb
    | true =>
      simp only [d43174, d311481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43175 q = 1) (hb : d310774 q = 1) : d311482 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43175, d311482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43175, d311482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43179 q = 1) (hb : d310774 q = 1) : d311486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98714 q ha hb
    | true =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43180 q = 1) (hb : d310774 q = 1) : d311487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43181 q = 1) (hb : d310774 q = 1) : d311488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43181, d311488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43181, d311488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43182 q = 1) (hb : d310774 q = 1) : d311489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43182, d311489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43182, d311489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43183 q = 1) (hb : d310774 q = 1) : d311490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43183, d311490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43183, d311490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43184 q = 1) (hb : d310774 q = 1) : d311491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43184, d311491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43184, d311491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98716 (p : Pattern) (ha : d43192 p = 1) (hb : d310774 p = 1) : d311499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43179 q = 1) (hb : d310774 q = 1) : d311486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98714 q ha hb
    | true =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43180 q = 1) (hb : d310774 q = 1) : d311487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43187 q = 1) (hb : d310774 q = 1) : d311494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d311494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98682 q ha hb
    | true =>
      simp only [d43187, d311494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43188 q = 1) (hb : d310774 q = 1) : d311495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d311495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43188, d311495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43189 q = 1) (hb : d310774 q = 1) : d311496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43189, d311496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43189, d311496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43190 q = 1) (hb : d310774 q = 1) : d311497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43190, d311497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43190, d311497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43191 q = 1) (hb : d310774 q = 1) : d311498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43191, d311498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43191, d311498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43192 q = 1) (hb : d310774 q = 1) : d311499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43192, d311499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43192, d311499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98717 (p : Pattern) (ha : d43246 p = 1) (hb : d310774 p = 1) : d311505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43179 q = 1) (hb : d310774 q = 1) : d311486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98714 q ha hb
    | true =>
      simp only [d43179, d311486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43180 q = 1) (hb : d310774 q = 1) : d311487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d311487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43243 q = 1) (hb : d310774 q = 1) : d311502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43243, d311502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43243, d311502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43244 q = 1) (hb : d310774 q = 1) : d311503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43244, d311503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43244, d311503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43245 q = 1) (hb : d310774 q = 1) : d311504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43245, d311504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43245, d311504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43246 q = 1) (hb : d310774 q = 1) : d311505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43246, d311505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43246, d311505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98718 (p : Pattern) (ha : d309910 p = 1) (hb : d310774 p = 1) : d311511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43193 q = 1) (hb : d310774 q = 1) : d311500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43193, d311500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98715 q ha hb
    | true =>
      simp only [d43193, d311500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98716 q ha hb
  have h2 (q : Pattern) (ha : d309906 q = 1) (hb : d310774 q = 1) : d311501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d311501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309906, d311501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43247 q = 1) (hb : d310774 q = 1) : d311506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43247, d311506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98717 q ha hb
    | true =>
      simp only [d43247, d311506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43248 q = 1) (hb : d310774 q = 1) : d311507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43248, d311507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43248, d311507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309907 q = 1) (hb : d310774 q = 1) : d311508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d311508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309907, d311508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309908 q = 1) (hb : d310774 q = 1) : d311509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d311509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309908, d311509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309909 q = 1) (hb : d310774 q = 1) : d311510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d311510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309909, d311510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309910 q = 1) (hb : d310774 q = 1) : d311511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d311511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309910, d311511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98719 (p : Pattern) (ha : d309916 p = 1) (hb : d310774 p = 1) : d311528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42905 q = 1) (hb : d310774 q = 1) : d311296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42905, d311296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42905, d311296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98673 q ha hb
  have h2 (q : Pattern) (ha : d42906 q = 1) (hb : d310774 q = 1) : d311297 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42906, d311297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42906, d311297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42915 q = 1) (hb : d310774 q = 1) : d311306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98673 q ha hb
    | true =>
      simp only [d42915, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98676 q ha hb
  have h4 (q : Pattern) (ha : d42916 q = 1) (hb : d310774 q = 1) : d311307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42916, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42917 q = 1) (hb : d310774 q = 1) : d311308 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42917, d311308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42917, d311308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309894 q = 1) (hb : d310774 q = 1) : d311412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d311412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98701 q ha hb
    | true =>
      simp only [d309894, d311412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98708 q ha hb
  have h7 (q : Pattern) (ha : d43118 q = 1) (hb : d310774 q = 1) : d311425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43118, d311425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98677 q ha hb
    | true =>
      simp only [d43118, d311425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98678 q ha hb
  have h8 (q : Pattern) (ha : d309895 q = 1) (hb : d310774 q = 1) : d311426 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d311426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309895, d311426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309896 q = 1) (hb : d310774 q = 1) : d311427 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d311427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309896, d311427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d309897 q = 1) (hb : d310774 q = 1) : d311428 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d311428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309897, d311428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309901 q = 1) (hb : d310774 q = 1) : d311432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d311432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309901, d311432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98709 q ha hb
  have h12 (q : Pattern) (ha : d43127 q = 1) (hb : d310774 q = 1) : d311434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43127, d311434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43127, d311434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98679 q ha hb
  have h13 (q : Pattern) (ha : d309902 q = 1) (hb : d310774 q = 1) : d311435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d311435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309902, d311435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309903 q = 1) (hb : d310774 q = 1) : d311436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d311436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309903, d311436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d309904 q = 1) (hb : d310774 q = 1) : d311437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d311437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309904, d311437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d309905 q = 1) (hb : d310774 q = 1) : d311438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d311438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309905, d311438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309911 q = 1) (hb : d310774 q = 1) : d311512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d311512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309911, d311512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98718 q ha hb
  have h18 (q : Pattern) (ha : d43264 q = 1) (hb : d310774 q = 1) : d311523 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43264, d311523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43264, d311523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98684 q ha hb
  have h19 (q : Pattern) (ha : d309912 q = 1) (hb : d310774 q = 1) : d311524 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d311524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309912, d311524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d309913 q = 1) (hb : d310774 q = 1) : d311525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d311525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309913, d311525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d309914 q = 1) (hb : d310774 q = 1) : d311526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d311526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309914, d311526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d309915 q = 1) (hb : d310774 q = 1) : d311527 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d311527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309915, d311527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d309916 q = 1) (hb : d310774 q = 1) : d311528 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d311528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309916, d311528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98720 (p : Pattern) (ha : d309922 p = 1) (hb : d310774 p = 1) : d311534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309917 q = 1) (hb : d310774 q = 1) : d311529 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d311529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309917, d311529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98719 q ha hb
  have h2 (q : Pattern) (ha : d309918 q = 1) (hb : d310774 q = 1) : d311530 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d311530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309918, d311530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309919 q = 1) (hb : d310774 q = 1) : d311531 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d311531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309919, d311531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309920 q = 1) (hb : d310774 q = 1) : d311532 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d311532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309920, d311532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309921 q = 1) (hb : d310774 q = 1) : d311533 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d311533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309921, d311533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309922 q = 1) (hb : d310774 q = 1) : d311534 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d311534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309922, d311534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98721 (p : Pattern) (ha : d43288 p = 1) (hb : d310774 p = 1) : d311547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42937 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98689 q ha hb
    | true =>
      simp only [d42937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42938 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1087 q = 1) (hb : d310774 q = 1) : d1087 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43278 q = 1) (hb : d310774 q = 1) : d311537 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43279 q = 1) (hb : d310774 q = 1) : d311538 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43280 q = 1) (hb : d310774 q = 1) : d311539 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d311539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43280, d311539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42942 q = 1) (hb : d310774 q = 1) : d43868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98690 q ha hb
    | true =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42943 q = 1) (hb : d310774 q = 1) : d43869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42946 q = 1) (hb : d310774 q = 1) : d311328 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d311328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98691 q ha hb
    | true =>
      simp only [d42946, d311328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42947 q = 1) (hb : d310774 q = 1) : d311329 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d311329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42947, d311329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42948 q = 1) (hb : d310774 q = 1) : d311330 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d311330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42948, d311330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43281 q = 1) (hb : d310774 q = 1) : d311540 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43281, d311540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43281, d311540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43282 q = 1) (hb : d310774 q = 1) : d311541 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43282, d311541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43282, d311541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1093 q = 1) (hb : d310774 q = 1) : d1093 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d43283 q = 1) (hb : d310774 q = 1) : d311542 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d43284 q = 1) (hb : d310774 q = 1) : d311543 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d43285 q = 1) (hb : d310774 q = 1) : d311544 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42951 q = 1) (hb : d310774 q = 1) : d311333 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d311333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42951, d311333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d43286 q = 1) (hb : d310774 q = 1) : d311545 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43286, d311545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d43286, d311545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d43287 q = 1) (hb : d310774 q = 1) : d311546 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43287, d311546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d43287, d311546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d43288 q = 1) (hb : d310774 q = 1) : d311547 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43288, d311547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43288, d311547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98722 (p : Pattern) (ha : d43300 p = 1) (hb : d310774 p = 1) : d311559 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d310774 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43278 q = 1) (hb : d310774 q = 1) : d311537 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43279 q = 1) (hb : d310774 q = 1) : d311538 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1093 q = 1) (hb : d310774 q = 1) : d1093 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43283 q = 1) (hb : d310774 q = 1) : d311542 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43284 q = 1) (hb : d310774 q = 1) : d311543 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d43285 q = 1) (hb : d310774 q = 1) : d311544 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42602 q = 1) (hb : d310774 q = 1) : d311074 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98637 q ha hb
    | true =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d42603 q = 1) (hb : d310774 q = 1) : d311075 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d42604 q = 1) (hb : d310774 q = 1) : d311076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43293 q = 1) (hb : d310774 q = 1) : d311552 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d311552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43293, d311552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43294 q = 1) (hb : d310774 q = 1) : d311553 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d311553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43294, d311553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d9771 q = 1) (hb : d310774 q = 1) : d9771 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d43295 q = 1) (hb : d310774 q = 1) : d311554 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d311554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98693 q ha hb
    | true =>
      simp only [d43295, d311554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43296 q = 1) (hb : d310774 q = 1) : d311555 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d311555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43296, d311555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d43297 q = 1) (hb : d310774 q = 1) : d311556 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d311556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d43297, d311556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h19 (q : Pattern) (ha : d43298 q = 1) (hb : d310774 q = 1) : d311557 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d311557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43298, d311557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d43299 q = 1) (hb : d310774 q = 1) : d311558 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d311558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43299, d311558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d43300 q = 1) (hb : d310774 q = 1) : d311559 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43300, d311559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43300, d311559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98723 (p : Pattern) (ha : d43309 p = 1) (hb : d310774 p = 1) : d311568 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d310774 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43278 q = 1) (hb : d310774 q = 1) : d311537 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43279 q = 1) (hb : d310774 q = 1) : d311538 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42962 q = 1) (hb : d310774 q = 1) : d311342 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98693 q ha hb
    | true =>
      simp only [d42962, d311342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d42963 q = 1) (hb : d310774 q = 1) : d311343 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42963, d311343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d43306 q = 1) (hb : d310774 q = 1) : d311565 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43306, d311565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43306, d311565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43307 q = 1) (hb : d310774 q = 1) : d311566 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43307, d311566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43307, d311566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d43308 q = 1) (hb : d310774 q = 1) : d311567 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43308, d311567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43308, d311567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d9771 q = 1) (hb : d310774 q = 1) : d9771 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d43295 q = 1) (hb : d310774 q = 1) : d311554 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d311554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98693 q ha hb
    | true =>
      simp only [d43295, d311554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43296 q = 1) (hb : d310774 q = 1) : d311555 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d311555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43296, d311555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d43297 q = 1) (hb : d310774 q = 1) : d311556 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d311556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43297, d311556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43298 q = 1) (hb : d310774 q = 1) : d311557 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d311557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43298, d311557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d43299 q = 1) (hb : d310774 q = 1) : d311558 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d311558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43299, d311558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d43309 q = 1) (hb : d310774 q = 1) : d311568 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43309, d311568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43309, d311568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro98724 (p : Pattern) (ha : d43318 p = 1) (hb : d310774 p = 1) : d311577 p = 1 := by
  have h0 (q : Pattern) (ha : d1093 q = 1) (hb : d310774 q = 1) : d1093 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43283 q = 1) (hb : d310774 q = 1) : d311542 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43284 q = 1) (hb : d310774 q = 1) : d311543 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d43314 q = 1) (hb : d310774 q = 1) : d311573 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43314, d311573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43314, d311573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43315 q = 1) (hb : d310774 q = 1) : d311574 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43315, d311574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43315, d311574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d43316 q = 1) (hb : d310774 q = 1) : d311575 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43316, d311575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43316, d311575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43317 q = 1) (hb : d310774 q = 1) : d311576 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43317, d311576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43317, d311576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d1119 q = 1) (hb : d310774 q = 1) : d1119 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d43318 q = 1) (hb : d310774 q = 1) : d311577 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43318, d311577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43318, d311577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98725 (p : Pattern) (ha : d43324 p = 1) (hb : d310774 p = 1) : d311583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43289 q = 1) (hb : d310774 q = 1) : d311548 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43289, d311548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98721 q ha hb
    | true =>
      simp only [d43289, d311548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43290 q = 1) (hb : d310774 q = 1) : d311549 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43290, d311549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43290, d311549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43291 q = 1) (hb : d310774 q = 1) : d311550 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43291, d311550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43291, d311550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43292 q = 1) (hb : d310774 q = 1) : d311551 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43292, d311551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43292, d311551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43301 q = 1) (hb : d310774 q = 1) : d311560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43301, d311560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98722 q ha hb
    | true =>
      simp only [d43301, d311560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43302 q = 1) (hb : d310774 q = 1) : d311561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43302, d311561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43302, d311561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43303 q = 1) (hb : d310774 q = 1) : d311562 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43303, d311562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43303, d311562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43304 q = 1) (hb : d310774 q = 1) : d311563 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43304, d311563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43304, d311563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43305 q = 1) (hb : d310774 q = 1) : d311564 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43305, d311564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43305, d311564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43310 q = 1) (hb : d310774 q = 1) : d311569 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d311569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98723 q ha hb
    | true =>
      simp only [d43310, d311569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43311 q = 1) (hb : d310774 q = 1) : d311570 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d311570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43311, d311570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43312 q = 1) (hb : d310774 q = 1) : d311571 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43312, d311571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43312, d311571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43313 q = 1) (hb : d310774 q = 1) : d311572 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43313, d311572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43313, d311572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43319 q = 1) (hb : d310774 q = 1) : d311578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98724 q ha hb
    | true =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43320 q = 1) (hb : d310774 q = 1) : d311579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43321 q = 1) (hb : d310774 q = 1) : d311580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d311580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43321, d311580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43322 q = 1) (hb : d310774 q = 1) : d311581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d311581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43322, d311581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43323 q = 1) (hb : d310774 q = 1) : d311582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43323, d311582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43323, d311582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43324 q = 1) (hb : d310774 q = 1) : d311583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43324, d311583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43324, d311583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro98726 (p : Pattern) (ha : d43330 p = 1) (hb : d310774 p = 1) : d311589 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d310774 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43278 q = 1) (hb : d310774 q = 1) : d311537 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98636 q ha hb
    | true =>
      simp only [d43278, d311537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43279 q = 1) (hb : d310774 q = 1) : d311538 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d311538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1093 q = 1) (hb : d310774 q = 1) : d1093 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43283 q = 1) (hb : d310774 q = 1) : d311542 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43284 q = 1) (hb : d310774 q = 1) : d311543 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d43285 q = 1) (hb : d310774 q = 1) : d311544 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43285, d311544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42602 q = 1) (hb : d310774 q = 1) : d311074 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98637 q ha hb
    | true =>
      simp only [d42602, d311074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d42603 q = 1) (hb : d310774 q = 1) : d311075 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42603, d311075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d42604 q = 1) (hb : d310774 q = 1) : d311076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42604, d311076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43293 q = 1) (hb : d310774 q = 1) : d311552 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d311552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43293, d311552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43294 q = 1) (hb : d310774 q = 1) : d311553 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d311553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43294, d311553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d18 q = 1) (hb : d310774 q = 1) : d18 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d43325 q = 1) (hb : d310774 q = 1) : d311584 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d311584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d43325, d311584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43326 q = 1) (hb : d310774 q = 1) : d311585 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d311585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43326, d311585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d43327 q = 1) (hb : d310774 q = 1) : d311586 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d311586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43327, d311586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d43328 q = 1) (hb : d310774 q = 1) : d311587 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d311587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43328, d311587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d43329 q = 1) (hb : d310774 q = 1) : d311588 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d311588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d43329, d311588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d43330 q = 1) (hb : d310774 q = 1) : d311589 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43330, d311589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43330, d311589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro98727 (p : Pattern) (ha : d43335 p = 1) (hb : d310774 p = 1) : d311594 p = 1 := by
  have h0 (q : Pattern) (ha : d1093 q = 1) (hb : d310774 q = 1) : d1093 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43283 q = 1) (hb : d310774 q = 1) : d311542 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98597 q ha hb
    | true =>
      simp only [d43283, d311542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43284 q = 1) (hb : d310774 q = 1) : d311543 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43284, d311543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18 q = 1) (hb : d310774 q = 1) : d18 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d43325 q = 1) (hb : d310774 q = 1) : d311584 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d311584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d43325, d311584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43326 q = 1) (hb : d310774 q = 1) : d311585 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d311585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43326, d311585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d43327 q = 1) (hb : d310774 q = 1) : d311586 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d311586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43327, d311586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d310774 q = 1) : d310777 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98578 q ha hb
    | true =>
      simp only [d42250, d310777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d310774 q = 1) : d310778 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d310778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d310774 q = 1) : d20 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42252 q = 1) (hb : d310774 q = 1) : d310779 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d310779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43328 q = 1) (hb : d310774 q = 1) : d311587 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d311587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43328, d311587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43329 q = 1) (hb : d310774 q = 1) : d311588 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d311588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43329, d311588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1119 q = 1) (hb : d310774 q = 1) : d1119 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d43335 q = 1) (hb : d310774 q = 1) : d311594 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43335, d311594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43335, d311594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98728 (p : Pattern) (ha : d43342 p = 1) (hb : d310774 p = 1) : d311601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43331 q = 1) (hb : d310774 q = 1) : d311590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d311590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98726 q ha hb
    | true =>
      simp only [d43331, d311590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43332 q = 1) (hb : d310774 q = 1) : d311591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d311591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43332, d311591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43333 q = 1) (hb : d310774 q = 1) : d311592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43333, d311592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43333, d311592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43334 q = 1) (hb : d310774 q = 1) : d311593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43334, d311593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43334, d311593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43336 q = 1) (hb : d310774 q = 1) : d311595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
    | true =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43337 q = 1) (hb : d310774 q = 1) : d311596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43338 q = 1) (hb : d310774 q = 1) : d311597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d311597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43338, d311597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43339 q = 1) (hb : d310774 q = 1) : d311598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d311598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43339, d311598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43340 q = 1) (hb : d310774 q = 1) : d311599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43340, d311599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43340, d311599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43319 q = 1) (hb : d310774 q = 1) : d311578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98724 q ha hb
    | true =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43320 q = 1) (hb : d310774 q = 1) : d311579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43321 q = 1) (hb : d310774 q = 1) : d311580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d311580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43321, d311580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43322 q = 1) (hb : d310774 q = 1) : d311581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d311581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43322, d311581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43341 q = 1) (hb : d310774 q = 1) : d311600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43341, d311600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43341, d311600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43342 q = 1) (hb : d310774 q = 1) : d311601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43342, d311601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43342, d311601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro98729 (p : Pattern) (ha : d43347 p = 1) (hb : d310774 p = 1) : d311606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43336 q = 1) (hb : d310774 q = 1) : d311595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
    | true =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43337 q = 1) (hb : d310774 q = 1) : d311596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43338 q = 1) (hb : d310774 q = 1) : d311597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d311597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43338, d311597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43339 q = 1) (hb : d310774 q = 1) : d311598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d311598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43339, d311598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43346 q = 1) (hb : d310774 q = 1) : d311605 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43346, d311605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43346, d311605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d310774 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d43347 q = 1) (hb : d310774 q = 1) : d311606 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43347, d311606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43347, d311606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro98730 (p : Pattern) (ha : d43354 p = 1) (hb : d310774 p = 1) : d311613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43343 q = 1) (hb : d310774 q = 1) : d311602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43343, d311602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98725 q ha hb
    | true =>
      simp only [d43343, d311602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98728 q ha hb
  have h2 (q : Pattern) (ha : d43344 q = 1) (hb : d310774 q = 1) : d311603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43344, d311603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43344, d311603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43345 q = 1) (hb : d310774 q = 1) : d311604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43345, d311604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43345, d311604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43348 q = 1) (hb : d310774 q = 1) : d311607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d311607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98728 q ha hb
    | true =>
      simp only [d43348, d311607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98729 q ha hb
  have h5 (q : Pattern) (ha : d43349 q = 1) (hb : d310774 q = 1) : d311608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d311608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43349, d311608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43350 q = 1) (hb : d310774 q = 1) : d311609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d311609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43350, d311609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43351 q = 1) (hb : d310774 q = 1) : d311610 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43351, d311610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43351, d311610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43352 q = 1) (hb : d310774 q = 1) : d311611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d311611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43352, d311611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43353 q = 1) (hb : d310774 q = 1) : d311612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43353, d311612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43353, d311612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43354 q = 1) (hb : d310774 q = 1) : d311613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43354, d311613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43354, d311613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro98731 (p : Pattern) (ha : d43358 p = 1) (hb : d310774 p = 1) : d311617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43348 q = 1) (hb : d310774 q = 1) : d311607 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d311607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98728 q ha hb
    | true =>
      simp only [d43348, d311607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98729 q ha hb
  have h2 (q : Pattern) (ha : d43349 q = 1) (hb : d310774 q = 1) : d311608 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d311608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43349, d311608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43350 q = 1) (hb : d310774 q = 1) : d311609 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d311609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43350, d311609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43352 q = 1) (hb : d310774 q = 1) : d311611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d311611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43352, d311611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43357 q = 1) (hb : d310774 q = 1) : d311616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43357, d311616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43357, d311616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43358 q = 1) (hb : d310774 q = 1) : d311617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43358, d311617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43358, d311617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98732 (p : Pattern) (ha : d43364 p = 1) (hb : d310774 p = 1) : d311623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d310774 q = 1) : d311614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98730 q ha hb
    | true =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d310774 q = 1) : d311615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d310774 q = 1) : d311620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d310774 q = 1) : d311621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43363 q = 1) (hb : d310774 q = 1) : d311622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d311622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d311622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43364 q = 1) (hb : d310774 q = 1) : d311623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43364, d311623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43364, d311623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98733 (p : Pattern) (ha : d43368 p = 1) (hb : d310774 p = 1) : d311627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d310774 q = 1) : d311624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d310774 q = 1) : d311625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43367 q = 1) (hb : d310774 q = 1) : d311626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d311626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d311626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43368 q = 1) (hb : d310774 q = 1) : d311627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43368, d311627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43368, d311627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98734 (p : Pattern) (ha : d43374 p = 1) (hb : d310774 p = 1) : d311633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d310774 q = 1) : d311628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98732 q ha hb
    | true =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98733 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d310774 q = 1) : d311629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d310774 q = 1) : d311630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d310774 q = 1) : d311631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d310774 q = 1) : d311632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43374 q = 1) (hb : d310774 q = 1) : d311633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43374, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43374, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98735 (p : Pattern) (ha : d43377 p = 1) (hb : d310774 p = 1) : d311636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d310774 q = 1) : d311614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98730 q ha hb
    | true =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d310774 q = 1) : d311615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d310774 q = 1) : d311620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d310774 q = 1) : d311621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43363 q = 1) (hb : d310774 q = 1) : d311622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d311622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d311622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43377 q = 1) (hb : d310774 q = 1) : d311636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43377, d311636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43377, d311636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro98736 (p : Pattern) (ha : d43378 p = 1) (hb : d310774 p = 1) : d311637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d310774 q = 1) : d311624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d310774 q = 1) : d311625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43367 q = 1) (hb : d310774 q = 1) : d311626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d311626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d311626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43378 q = 1) (hb : d310774 q = 1) : d311637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43378, d311637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43378, d311637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98737 (p : Pattern) (ha : d43384 p = 1) (hb : d310774 p = 1) : d311643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d310774 q = 1) : d311628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98732 q ha hb
    | true =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98733 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d310774 q = 1) : d311629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d310774 q = 1) : d311630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d310774 q = 1) : d311631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d310774 q = 1) : d311632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43379 q = 1) (hb : d310774 q = 1) : d311638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98735 q ha hb
    | true =>
      simp only [d43379, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98736 q ha hb
  have h7 (q : Pattern) (ha : d43380 q = 1) (hb : d310774 q = 1) : d311639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43380, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43381 q = 1) (hb : d310774 q = 1) : d311640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43381, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43382 q = 1) (hb : d310774 q = 1) : d311641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43382, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43383 q = 1) (hb : d310774 q = 1) : d311642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43383, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43384 q = 1) (hb : d310774 q = 1) : d311643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43384, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43384, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98738 (p : Pattern) (ha : d43630 p = 1) (hb : d310774 p = 1) : d311769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d310774 q = 1) : d311628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98732 q ha hb
    | true =>
      simp only [d43369, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98733 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d310774 q = 1) : d311629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d310774 q = 1) : d311630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d310774 q = 1) : d311631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d310774 q = 1) : d311632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43625 q = 1) (hb : d310774 q = 1) : d311764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d311764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98733 q ha hb
    | true =>
      simp only [d43625, d311764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43626 q = 1) (hb : d310774 q = 1) : d311765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d311765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43626, d311765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43627 q = 1) (hb : d310774 q = 1) : d311766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d311766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43627, d311766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43628 q = 1) (hb : d310774 q = 1) : d311767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d311767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43628, d311767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43629 q = 1) (hb : d310774 q = 1) : d311768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d311768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43629, d311768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43630 q = 1) (hb : d310774 q = 1) : d311769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43630, d311769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43630, d311769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98739 (p : Pattern) (ha : d43636 p = 1) (hb : d310774 p = 1) : d311775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43625 q = 1) (hb : d310774 q = 1) : d311764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d311764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98733 q ha hb
    | true =>
      simp only [d43625, d311764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43626 q = 1) (hb : d310774 q = 1) : d311765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d311765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43626, d311765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43627 q = 1) (hb : d310774 q = 1) : d311766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d311766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43627, d311766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43628 q = 1) (hb : d310774 q = 1) : d311767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d311767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43628, d311767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43629 q = 1) (hb : d310774 q = 1) : d311768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d311768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43629, d311768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43631 q = 1) (hb : d310774 q = 1) : d311770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d311770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98736 q ha hb
    | true =>
      simp only [d43631, d311770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43632 q = 1) (hb : d310774 q = 1) : d311771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d311771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43632, d311771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43633 q = 1) (hb : d310774 q = 1) : d311772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d311772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43633, d311772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43634 q = 1) (hb : d310774 q = 1) : d311773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d311773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43634, d311773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43635 q = 1) (hb : d310774 q = 1) : d311774 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d311774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43635, d311774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43636 q = 1) (hb : d310774 q = 1) : d311775 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43636, d311775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43636, d311775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro98740 (p : Pattern) (ha : d43645 p = 1) (hb : d310774 p = 1) : d311784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43631 q = 1) (hb : d310774 q = 1) : d311770 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d311770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98736 q ha hb
    | true =>
      simp only [d43631, d311770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43632 q = 1) (hb : d310774 q = 1) : d311771 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d311771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43632, d311771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43633 q = 1) (hb : d310774 q = 1) : d311772 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d311772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43633, d311772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43634 q = 1) (hb : d310774 q = 1) : d311773 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d311773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43634, d311773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43635 q = 1) (hb : d310774 q = 1) : d311774 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d311774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43635, d311774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43645 q = 1) (hb : d310774 q = 1) : d311784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43645, d311784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43645, d311784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98741 (p : Pattern) (ha : d43708 p = 1) (hb : d310774 p = 1) : d311847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43699 q = 1) (hb : d310774 q = 1) : d311838 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43699, d311838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43699, d311838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98726 q ha hb
  have h2 (q : Pattern) (ha : d43331 q = 1) (hb : d310774 q = 1) : d311590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d311590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98726 q ha hb
    | true =>
      simp only [d43331, d311590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43700 q = 1) (hb : d310774 q = 1) : d311839 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43700, d311839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43700, d311839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43332 q = 1) (hb : d310774 q = 1) : d311591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d311591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43332, d311591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43701 q = 1) (hb : d310774 q = 1) : d311840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43701, d311840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43701, d311840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43702 q = 1) (hb : d310774 q = 1) : d311841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43702, d311841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43702, d311841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43703 q = 1) (hb : d310774 q = 1) : d311842 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43703, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
  have h8 (q : Pattern) (ha : d43336 q = 1) (hb : d310774 q = 1) : d311595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
    | true =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43704 q = 1) (hb : d310774 q = 1) : d311843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43704, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43337 q = 1) (hb : d310774 q = 1) : d311596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43705 q = 1) (hb : d310774 q = 1) : d311844 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43705, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43706 q = 1) (hb : d310774 q = 1) : d311845 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43706, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43707 q = 1) (hb : d310774 q = 1) : d311846 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43707, d311846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43707, d311846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43679 q = 1) (hb : d310774 q = 1) : d311818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43679, d311818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43679, d311818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98724 q ha hb
  have h15 (q : Pattern) (ha : d43319 q = 1) (hb : d310774 q = 1) : d311578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98724 q ha hb
    | true =>
      simp only [d43319, d311578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43680 q = 1) (hb : d310774 q = 1) : d311819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43680, d311819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43680, d311819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43320 q = 1) (hb : d310774 q = 1) : d311579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43320, d311579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43681 q = 1) (hb : d310774 q = 1) : d311820 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43681, d311820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43681, d311820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43682 q = 1) (hb : d310774 q = 1) : d311821 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43682, d311821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43682, d311821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d43693 q = 1) (hb : d310774 q = 1) : d311832 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43693, d311832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43693, d311832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d43708 q = 1) (hb : d310774 q = 1) : d311847 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43708, d311847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43708, d311847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro98742 (p : Pattern) (ha : d43713 p = 1) (hb : d310774 p = 1) : d311852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43703 q = 1) (hb : d310774 q = 1) : d311842 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43703, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
  have h2 (q : Pattern) (ha : d43336 q = 1) (hb : d310774 q = 1) : d311595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98727 q ha hb
    | true =>
      simp only [d43336, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43704 q = 1) (hb : d310774 q = 1) : d311843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43704, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43337 q = 1) (hb : d310774 q = 1) : d311596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43337, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43705 q = 1) (hb : d310774 q = 1) : d311844 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43705, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43706 q = 1) (hb : d310774 q = 1) : d311845 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43706, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43712 q = 1) (hb : d310774 q = 1) : d311851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43712, d311851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43712, d311851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d310774 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d43713 q = 1) (hb : d310774 q = 1) : d311852 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43713, d311852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43713, d311852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro98743 (p : Pattern) (ha : d43732 p = 1) (hb : d310774 p = 1) : d311871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43714 q = 1) (hb : d310774 q = 1) : d311853 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d311853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98741 q ha hb
    | true =>
      simp only [d43714, d311853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98742 q ha hb
  have h2 (q : Pattern) (ha : d43715 q = 1) (hb : d310774 q = 1) : d311854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d311854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43715, d311854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43716 q = 1) (hb : d310774 q = 1) : d311855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d311855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43716, d311855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43722 q = 1) (hb : d310774 q = 1) : d311861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43722, d311861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43722, d311861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43731 q = 1) (hb : d310774 q = 1) : d311870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43731, d311870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43731, d311870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43732 q = 1) (hb : d310774 q = 1) : d311871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43732, d311871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43732, d311871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98744 (p : Pattern) (ha : d43821 p = 1) (hb : d310774 p = 1) : d311903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43733 q = 1) (hb : d310774 q = 1) : d311872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43733, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98743 q ha hb
    | true =>
      simp only [d43733, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43734 q = 1) (hb : d310774 q = 1) : d311873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43734, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43734, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43818 q = 1) (hb : d310774 q = 1) : d311900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43818, d311900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43818, d311900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43819 q = 1) (hb : d310774 q = 1) : d311901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43819, d311901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43819, d311901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43820 q = 1) (hb : d310774 q = 1) : d311902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43820, d311902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43820, d311902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43821 q = 1) (hb : d310774 q = 1) : d311903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43821, d311903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43821, d311903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro98745 (p : Pattern) (ha : d43827 p = 1) (hb : d310774 p = 1) : d311909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43822 q = 1) (hb : d310774 q = 1) : d311904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43822, d311904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98744 q ha hb
    | true =>
      simp only [d43822, d311904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43823 q = 1) (hb : d310774 q = 1) : d311905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43823, d311905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43823, d311905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43824 q = 1) (hb : d310774 q = 1) : d311906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43824, d311906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43824, d311906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43825 q = 1) (hb : d310774 q = 1) : d311907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43825, d311907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43825, d311907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43826 q = 1) (hb : d310774 q = 1) : d311908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43826, d311908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43826, d311908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43827 q = 1) (hb : d310774 q = 1) : d311909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43827, d311909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43827, d311909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98746 (p : Pattern) (ha : d43389 p = 1) (hb : d310774 p = 1) : d311648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d310774 q = 1) : d311614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98730 q ha hb
    | true =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d310774 q = 1) : d311615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d310774 q = 1) : d311620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d310774 q = 1) : d311621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d311621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43388 q = 1) (hb : d310774 q = 1) : d311647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43388, d311647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43388, d311647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43389 q = 1) (hb : d310774 q = 1) : d311648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43389, d311648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43389, d311648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98747 (p : Pattern) (ha : d43391 p = 1) (hb : d310774 p = 1) : d311650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d310774 q = 1) : d311624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d310774 q = 1) : d311625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d311625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43390 q = 1) (hb : d310774 q = 1) : d311649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43390, d311649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43390, d311649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43391 q = 1) (hb : d310774 q = 1) : d311650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43391, d311650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43391, d311650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro98748 (p : Pattern) (ha : d43398 p = 1) (hb : d310774 p = 1) : d311657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d310774 q = 1) : d311614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98730 q ha hb
    | true =>
      simp only [d43355, d311614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d310774 q = 1) : d311615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d311615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d310774 q = 1) : d311620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d311620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43396 q = 1) (hb : d310774 q = 1) : d311655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43396, d311655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43396, d311655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43397 q = 1) (hb : d310774 q = 1) : d311656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43397, d311656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43397, d311656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43398 q = 1) (hb : d310774 q = 1) : d311657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43398, d311657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43398, d311657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro98749 (p : Pattern) (ha : d43401 p = 1) (hb : d310774 p = 1) : d311660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d310774 q = 1) : d311618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro98731 q ha hb
    | true =>
      simp only [d43359, d311618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d310774 q = 1) : d311619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d311619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d310774 q = 1) : d311624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d311624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43399 q = 1) (hb : d310774 q = 1) : d311658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43399, d311658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43399, d311658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43400 q = 1) (hb : d310774 q = 1) : d311659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43400, d311659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43400, d311659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43401 q = 1) (hb : d310774 q = 1) : d311660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43401, d311660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43401, d311660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
