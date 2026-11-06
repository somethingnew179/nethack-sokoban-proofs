import NetHack.Soko22Hazard87.AndIntroBlocks0089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro22500 (p : Pattern) (ha : d123860 p = 1) (hb : d125394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d125389 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22499 q ha hb
    | true =>
      simp only [d123855, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d125390 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d125391 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d125392 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d125393 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d125394 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22501 (p : Pattern) (ha : d123866 p = 1) (hb : d125400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d125395 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22500 q ha hb
    | true =>
      simp only [d123861, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d125396 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d125397 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d125398 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d125399 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d125400 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22502 (p : Pattern) (ha : d123872 p = 1) (hb : d125406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d125401 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22501 q ha hb
    | true =>
      simp only [d123867, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d125402 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d125403 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d125404 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d125405 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d125406 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22503 (p : Pattern) (ha : d123878 p = 1) (hb : d125412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d125407 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22502 q ha hb
    | true =>
      simp only [d123873, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d125408 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d125409 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d125410 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d125411 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d125412 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22504 (p : Pattern) (ha : d104 p = 1) (hb : d125417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d125417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22505 (p : Pattern) (ha : d111 p = 1) (hb : d125422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d125420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d125421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d125422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22506 (p : Pattern) (ha : d406 p = 1) (hb : d125429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d125427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d125428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d125429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22507 (p : Pattern) (ha : d462 p = 1) (hb : d125439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d125435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d125436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d125437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d125438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d125439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22508 (p : Pattern) (ha : d53647 p = 1) (hb : d125445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d125423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22504 q ha hb
    | true =>
      simp only [d112, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22505 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d125424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d125425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d125426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d125430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22506 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d125431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d125432 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d125433 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d125434 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d125440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22507 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d125441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d125442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d125443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d125444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d125445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22509 (p : Pattern) (ha : d123951 p = 1) (hb : d125455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123947 q = 1) (hb : d125451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123947, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123947, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123948 q = 1) (hb : d125452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123948, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123948, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123949 q = 1) (hb : d125453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123949, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123949, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123950 q = 1) (hb : d125454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123950, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123950, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123951 q = 1) (hb : d125455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123951, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123951, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22510 (p : Pattern) (ha : d123958 p = 1) (hb : d125460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123947 q = 1) (hb : d125451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123947, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123947, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123948 q = 1) (hb : d125452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123948, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123948, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123949 q = 1) (hb : d125453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123949, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123949, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123950 q = 1) (hb : d125454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123950, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123950, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d123954 q = 1) (hb : d125456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123954, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123954, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123955 q = 1) (hb : d125457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123955, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123955, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123956 q = 1) (hb : d125458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123956, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123956, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123957 q = 1) (hb : d125459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123957, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123957, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123958 q = 1) (hb : d125460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123958, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123958, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22511 (p : Pattern) (ha : d125190 p = 1) (hb : d125467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123954 q = 1) (hb : d125456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123954, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123954, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123955 q = 1) (hb : d125457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123955, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123955, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123956 q = 1) (hb : d125465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123956, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123956, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123957 q = 1) (hb : d125466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123957, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123957, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125190 q = 1) (hb : d125467 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125190, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125190, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22512 (p : Pattern) (ha : d125200 p = 1) (hb : d125477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125196 q = 1) (hb : d125473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125196, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125196, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14191 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125197 q = 1) (hb : d125474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125197, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125197, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125198 q = 1) (hb : d125475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125198, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125198, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125199 q = 1) (hb : d125476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125199, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125199, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125200 q = 1) (hb : d125477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125200, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125200, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22513 (p : Pattern) (ha : d125206 p = 1) (hb : d125483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123959 q = 1) (hb : d125461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123959, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22509 q ha hb
    | true =>
      simp only [d123959, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22510 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123960 q = 1) (hb : d125462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123960, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123960, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125188 q = 1) (hb : d125463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125188, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125188, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125189 q = 1) (hb : d125464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125189, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125189, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125191 q = 1) (hb : d125468 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125191, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125191, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22511 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125192 q = 1) (hb : d125469 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125192, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125192, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125193 q = 1) (hb : d125470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125193, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125193, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125194 q = 1) (hb : d125471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125194, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125194, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125195 q = 1) (hb : d125472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125195, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125195, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125201 q = 1) (hb : d125478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125201, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125201, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22512 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125202 q = 1) (hb : d125479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125202, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125202, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125203 q = 1) (hb : d125480 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125203, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125203, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125204 q = 1) (hb : d125481 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125204, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125204, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125205 q = 1) (hb : d125482 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125205, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125205, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125206 q = 1) (hb : d125483 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125206, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125206, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22514 (p : Pattern) (ha : d125212 p = 1) (hb : d125489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d125446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22508 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d125447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d125448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d125449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d125450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125207 q = 1) (hb : d125484 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125207, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125207, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22513 q ha hb
  have h8 (q : Pattern) (ha : d125208 q = 1) (hb : d125485 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125208, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125208, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125209 q = 1) (hb : d125486 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125209, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125209, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125210 q = 1) (hb : d125487 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125210, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125210, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125211 q = 1) (hb : d125488 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125211, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125211, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125212 q = 1) (hb : d125489 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125212, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125212, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22515 (p : Pattern) (ha : d124086 p = 1) (hb : d125494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124082 q = 1) (hb : d125490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124082, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124082, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d124083 q = 1) (hb : d125491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124083, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d124083, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124084 q = 1) (hb : d125492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124084, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124084, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d124085 q = 1) (hb : d125493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124085, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124085, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d124086 q = 1) (hb : d125494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124086, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124086, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22516 (p : Pattern) (ha : d124096 p = 1) (hb : d125499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d124082 q = 1) (hb : d125490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124082, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124082, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d124083 q = 1) (hb : d125491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124083, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d124083, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124084 q = 1) (hb : d125492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124084, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124084, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124085 q = 1) (hb : d125493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124085, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124085, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d124092 q = 1) (hb : d125495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124092, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d124092, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d124093 q = 1) (hb : d125496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124093, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d124093, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d124094 q = 1) (hb : d125497 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124094, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d124094, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d124095 q = 1) (hb : d125498 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124095, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d124095, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d124096 q = 1) (hb : d125499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124096, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d124096, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22517 (p : Pattern) (ha : d125215 p = 1) (hb : d125506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124092 q = 1) (hb : d125495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124092, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124092, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124093 q = 1) (hb : d125496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124093, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124093, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124094 q = 1) (hb : d125504 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124094, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124094, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124095 q = 1) (hb : d125505 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124095, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124095, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125215 q = 1) (hb : d125506 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125215, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125215, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22518 (p : Pattern) (ha : d125226 p = 1) (hb : d125516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125221 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125222 q = 1) (hb : d125512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125222, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125222, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125223 q = 1) (hb : d125513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125223, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125223, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125224 q = 1) (hb : d125514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125224, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125224, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125225 q = 1) (hb : d125515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125225, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125225, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125226 q = 1) (hb : d125516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125226, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125226, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22519 (p : Pattern) (ha : d125232 p = 1) (hb : d125522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124097 q = 1) (hb : d125500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d124097, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22515 q ha hb
    | true =>
      simp only [d124097, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22516 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124098 q = 1) (hb : d125501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d124098, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124098, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125213 q = 1) (hb : d125502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125213, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125213, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125214 q = 1) (hb : d125503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125214, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125214, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125216 q = 1) (hb : d125507 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125216, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125216, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22517 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125217 q = 1) (hb : d125508 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125217, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125217, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125218 q = 1) (hb : d125509 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125218, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125218, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125219 q = 1) (hb : d125510 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125219, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125219, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125220 q = 1) (hb : d125511 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125220, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125220, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125227 q = 1) (hb : d125517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125227, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125227, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22518 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125228 q = 1) (hb : d125518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125228, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125228, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125229 q = 1) (hb : d125519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125229, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125229, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125230 q = 1) (hb : d125520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125230, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125230, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125231 q = 1) (hb : d125521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125231, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125231, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125232 q = 1) (hb : d125522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125232, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125232, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22520 (p : Pattern) (ha : d125238 p = 1) (hb : d125528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125233 q = 1) (hb : d125523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125233, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125233, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22519 q ha hb
  have h2 (q : Pattern) (ha : d125234 q = 1) (hb : d125524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125234, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125234, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125235 q = 1) (hb : d125525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125235, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125235, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125236 q = 1) (hb : d125526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125236, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125236, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125237 q = 1) (hb : d125527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125237, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125237, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125238 q = 1) (hb : d125528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125238, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125238, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22521 (p : Pattern) (ha : d124272 p = 1) (hb : d125534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124268 q = 1) (hb : d125530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124268, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124268, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d124269 q = 1) (hb : d125531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124269, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d124269, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124270 q = 1) (hb : d125532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124270, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124270, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d124271 q = 1) (hb : d125533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124271, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124271, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d124272 q = 1) (hb : d125534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124272, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124272, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22522 (p : Pattern) (ha : d124282 p = 1) (hb : d125539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d124268 q = 1) (hb : d125530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124268, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124268, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d124269 q = 1) (hb : d125531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124269, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d124269, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124270 q = 1) (hb : d125532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124270, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124270, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124271 q = 1) (hb : d125533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124271, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124271, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d124278 q = 1) (hb : d125535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124278, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d124278, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d124279 q = 1) (hb : d125536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124279, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d124279, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d124280 q = 1) (hb : d125537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124280, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d124280, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d124281 q = 1) (hb : d125538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124281, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d124281, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d124282 q = 1) (hb : d125539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124282, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d124282, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22523 (p : Pattern) (ha : d125242 p = 1) (hb : d125546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124278 q = 1) (hb : d125535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124278, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124278, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124279 q = 1) (hb : d125536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124279, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124279, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124280 q = 1) (hb : d125544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124280, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124280, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124281 q = 1) (hb : d125545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124281, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124281, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125242 q = 1) (hb : d125546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125242, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125242, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22524 (p : Pattern) (ha : d125253 p = 1) (hb : d125556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125249 q = 1) (hb : d125552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125249, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125249, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125250 q = 1) (hb : d125553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125250, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125250, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125251 q = 1) (hb : d125554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125251, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125251, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125252 q = 1) (hb : d125555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125252, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125252, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125253 q = 1) (hb : d125556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125253, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125253, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22525 (p : Pattern) (ha : d125259 p = 1) (hb : d125562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124283 q = 1) (hb : d125540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d124283, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22521 q ha hb
    | true =>
      simp only [d124283, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22522 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124284 q = 1) (hb : d125541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d124284, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124284, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125240 q = 1) (hb : d125542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125240, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125240, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125241 q = 1) (hb : d125543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125241, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125241, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125243 q = 1) (hb : d125547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125243, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125243, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22523 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14638 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125244 q = 1) (hb : d125548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125244, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125244, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125245 q = 1) (hb : d125549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125245, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125245, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125246 q = 1) (hb : d125550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125246, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125246, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125247 q = 1) (hb : d125551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125247, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125247, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125254 q = 1) (hb : d125557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125254, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125254, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22524 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125255 q = 1) (hb : d125558 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125255, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125255, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125256 q = 1) (hb : d125559 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125256, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125256, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125257 q = 1) (hb : d125560 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125257, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125257, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125258 q = 1) (hb : d125561 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125258, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125258, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125259 q = 1) (hb : d125562 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125259, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125259, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22526 (p : Pattern) (ha : d125265 p = 1) (hb : d125568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125260 q = 1) (hb : d125563 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125260, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125260, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22525 q ha hb
  have h2 (q : Pattern) (ha : d125261 q = 1) (hb : d125564 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125261, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125261, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125262 q = 1) (hb : d125565 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125262, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125262, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125263 q = 1) (hb : d125566 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125263, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125263, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125264 q = 1) (hb : d125567 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125264, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125264, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125265 q = 1) (hb : d125568 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125265, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125265, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22527 (p : Pattern) (ha : d124473 p = 1) (hb : d125575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124469 q = 1) (hb : d125571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124469, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124469, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d124470 q = 1) (hb : d125572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124470, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d124470, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124471 q = 1) (hb : d125573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124471, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124471, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d124472 q = 1) (hb : d125574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124472, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124472, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d124473 q = 1) (hb : d125575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124473, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124473, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22528 (p : Pattern) (ha : d124483 p = 1) (hb : d125580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d124469 q = 1) (hb : d125571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124469, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124469, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d124470 q = 1) (hb : d125572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124470, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d124470, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124471 q = 1) (hb : d125573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124471, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124471, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124472 q = 1) (hb : d125574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124472, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124472, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14934 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14939 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d124479 q = 1) (hb : d125576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124479, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d124479, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d124480 q = 1) (hb : d125577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124480, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d124480, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d124481 q = 1) (hb : d125578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124481, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d124481, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d124482 q = 1) (hb : d125579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124482, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d124482, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d124483 q = 1) (hb : d125580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124483, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d124483, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22529 (p : Pattern) (ha : d125270 p = 1) (hb : d125587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124479 q = 1) (hb : d125576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124479, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124479, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124480 q = 1) (hb : d125577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124480, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124480, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124481 q = 1) (hb : d125585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124481, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124481, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124482 q = 1) (hb : d125586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124482, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124482, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125270 q = 1) (hb : d125587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125270, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125270, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22530 (p : Pattern) (ha : d125285 p = 1) (hb : d125597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125281 q = 1) (hb : d125593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125281, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125281, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125282 q = 1) (hb : d125594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125282, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125282, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125283 q = 1) (hb : d125595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125283, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125283, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125284 q = 1) (hb : d125596 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125284, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125284, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125285 q = 1) (hb : d125597 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125285, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125285, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22531 (p : Pattern) (ha : d125291 p = 1) (hb : d125603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124484 q = 1) (hb : d125581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d124484, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22527 q ha hb
    | true =>
      simp only [d124484, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22528 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124485 q = 1) (hb : d125582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d124485, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124485, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125268 q = 1) (hb : d125583 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125268, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125268, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125269 q = 1) (hb : d125584 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125269, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125269, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125271 q = 1) (hb : d125588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125271, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125271, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22529 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14981 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125272 q = 1) (hb : d125589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125272, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125272, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125273 q = 1) (hb : d125590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125273, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125273, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125274 q = 1) (hb : d125591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125274, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125274, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125275 q = 1) (hb : d125592 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125275, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125275, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125286 q = 1) (hb : d125598 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125286, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125286, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22530 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125287 q = 1) (hb : d125599 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125287, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125287, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125288 q = 1) (hb : d125600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125288, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125288, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125289 q = 1) (hb : d125601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125289, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125289, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125290 q = 1) (hb : d125602 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125290, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125290, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125291 q = 1) (hb : d125603 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125291, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125291, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22532 (p : Pattern) (ha : d125297 p = 1) (hb : d125609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125292 q = 1) (hb : d125604 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125292, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125292, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22531 q ha hb
  have h2 (q : Pattern) (ha : d125293 q = 1) (hb : d125605 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125293, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125293, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125294 q = 1) (hb : d125606 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125294, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125294, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125295 q = 1) (hb : d125607 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125295, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125295, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125296 q = 1) (hb : d125608 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125296, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125296, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125297 q = 1) (hb : d125609 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125297, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125297, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22533 (p : Pattern) (ha : d124707 p = 1) (hb : d125617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124703 q = 1) (hb : d125613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124703, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124703, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d124704 q = 1) (hb : d125614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124704, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d124704, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124705 q = 1) (hb : d125615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124705, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124705, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d124706 q = 1) (hb : d125616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124706, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124706, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d124707 q = 1) (hb : d125617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124707, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124707, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22534 (p : Pattern) (ha : d124717 p = 1) (hb : d125622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d124703 q = 1) (hb : d125613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124703, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124703, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d124704 q = 1) (hb : d125614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124704, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d124704, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124705 q = 1) (hb : d125615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124705, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124705, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124706 q = 1) (hb : d125616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124706, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124706, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d124713 q = 1) (hb : d125618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124713, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d124713, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d124714 q = 1) (hb : d125619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124714, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d124714, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d124715 q = 1) (hb : d125620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124715, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d124715, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d124716 q = 1) (hb : d125621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124716, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d124716, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d124717 q = 1) (hb : d125622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124717, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d124717, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22535 (p : Pattern) (ha : d125303 p = 1) (hb : d125629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124713 q = 1) (hb : d125618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124713, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124713, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124714 q = 1) (hb : d125619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124714, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124714, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124715 q = 1) (hb : d125627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124715, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124715, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124716 q = 1) (hb : d125628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124716, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124716, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125303 q = 1) (hb : d125629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125303, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125303, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22536 (p : Pattern) (ha : d125318 p = 1) (hb : d125639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125314 q = 1) (hb : d125635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125314, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125314, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125315 q = 1) (hb : d125636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125315, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125315, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125316 q = 1) (hb : d125637 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125316, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125316, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125317 q = 1) (hb : d125638 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125317, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125317, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125318 q = 1) (hb : d125639 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125318, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125318, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22537 (p : Pattern) (ha : d125324 p = 1) (hb : d125645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124718 q = 1) (hb : d125623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d124718, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22533 q ha hb
    | true =>
      simp only [d124718, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22534 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15365 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124719 q = 1) (hb : d125624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d124719, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124719, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125301 q = 1) (hb : d125625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125301, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125301, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125302 q = 1) (hb : d125626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125302, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125302, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125304 q = 1) (hb : d125630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125304, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125304, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22535 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15374 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125305 q = 1) (hb : d125631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125305, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125305, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125306 q = 1) (hb : d125632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125306, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125306, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125307 q = 1) (hb : d125633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125307, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125307, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125308 q = 1) (hb : d125634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125308, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125308, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125319 q = 1) (hb : d125640 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125319, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125319, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22536 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15528 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125320 q = 1) (hb : d125641 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125320, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125320, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125321 q = 1) (hb : d125642 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125321, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125321, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125322 q = 1) (hb : d125643 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125322, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125322, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125323 q = 1) (hb : d125644 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125323, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125323, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125324 q = 1) (hb : d125645 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125324, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125324, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22538 (p : Pattern) (ha : d125330 p = 1) (hb : d125651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125325 q = 1) (hb : d125646 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125325, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125325, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22537 q ha hb
  have h2 (q : Pattern) (ha : d125326 q = 1) (hb : d125647 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125326, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125326, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125327 q = 1) (hb : d125648 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125327, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125327, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125328 q = 1) (hb : d125649 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125328, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125328, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125329 q = 1) (hb : d125650 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125329, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125329, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125330 q = 1) (hb : d125651 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125330, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125330, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22539 (p : Pattern) (ha : d124942 p = 1) (hb : d125660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124938 q = 1) (hb : d125656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124938, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124938, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d124939 q = 1) (hb : d125657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124939, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d124939, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124940 q = 1) (hb : d125658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124940, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124940, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d124941 q = 1) (hb : d125659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124941, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124941, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d124942 q = 1) (hb : d125660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124942, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124942, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22540 (p : Pattern) (ha : d124952 p = 1) (hb : d125665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d124938 q = 1) (hb : d125656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124938, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d124938, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d124939 q = 1) (hb : d125657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124939, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d124939, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124940 q = 1) (hb : d125658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124940, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124940, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d124941 q = 1) (hb : d125659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124941, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124941, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15715 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15720 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d124948 q = 1) (hb : d125661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124948, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d124948, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d124949 q = 1) (hb : d125662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124949, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d124949, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d124950 q = 1) (hb : d125663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124950, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d124950, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d124951 q = 1) (hb : d125664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124951, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d124951, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d124952 q = 1) (hb : d125665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d124952, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d124952, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22541 (p : Pattern) (ha : d125337 p = 1) (hb : d125672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124948 q = 1) (hb : d125661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d124948, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124948, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d124949 q = 1) (hb : d125662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d124949, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d124949, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124950 q = 1) (hb : d125670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d124950, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124950, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d124951 q = 1) (hb : d125671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d124951, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d124951, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125337 q = 1) (hb : d125672 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125337, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125337, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22542 (p : Pattern) (ha : d125352 p = 1) (hb : d125682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125347 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125348 q = 1) (hb : d125678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125348, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125348, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125349 q = 1) (hb : d125679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125349, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125349, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125350 q = 1) (hb : d125680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125350, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125350, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125351 q = 1) (hb : d125681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125351, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125351, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125352 q = 1) (hb : d125682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125352, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125352, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22543 (p : Pattern) (ha : d125358 p = 1) (hb : d125688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d124953 q = 1) (hb : d125666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d124953, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22539 q ha hb
    | true =>
      simp only [d124953, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22540 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124954 q = 1) (hb : d125667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d124954, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d124954, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125335 q = 1) (hb : d125668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125335, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125335, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125336 q = 1) (hb : d125669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125336, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125336, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125338 q = 1) (hb : d125673 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125338, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125338, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22541 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125339 q = 1) (hb : d125674 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125339, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125339, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125340 q = 1) (hb : d125675 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125340, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125340, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125341 q = 1) (hb : d125676 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125341, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125341, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125342 q = 1) (hb : d125677 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125342, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125342, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125353 q = 1) (hb : d125683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125353, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125353, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22542 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15906 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125354 q = 1) (hb : d125684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125354, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125354, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125355 q = 1) (hb : d125685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125355, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125355, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125356 q = 1) (hb : d125686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125356, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125356, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125357 q = 1) (hb : d125687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125357, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125357, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125358 q = 1) (hb : d125688 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125358, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125358, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22544 (p : Pattern) (ha : d125364 p = 1) (hb : d125694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125359 q = 1) (hb : d125689 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125359, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125359, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22543 q ha hb
  have h2 (q : Pattern) (ha : d125360 q = 1) (hb : d125690 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125360, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125360, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125361 q = 1) (hb : d125691 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125361, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125361, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125362 q = 1) (hb : d125692 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125362, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125362, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125363 q = 1) (hb : d125693 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125363, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125363, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125364 q = 1) (hb : d125694 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125364, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125364, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22545 (p : Pattern) (ha : d125370 p = 1) (hb : d125700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125239 q = 1) (hb : d125529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125239, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22514 q ha hb
    | true =>
      simp only [d125239, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22520 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125266 q = 1) (hb : d125569 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125266, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125266, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22526 q ha hb
  have h3 (q : Pattern) (ha : d125267 q = 1) (hb : d125570 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125267, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125267, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125298 q = 1) (hb : d125610 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125298, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125298, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22532 q ha hb
  have h5 (q : Pattern) (ha : d125299 q = 1) (hb : d125611 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125299, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125299, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125300 q = 1) (hb : d125612 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125300, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125300, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125331 q = 1) (hb : d125652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125331, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125331, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22538 q ha hb
  have h8 (q : Pattern) (ha : d125332 q = 1) (hb : d125653 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125332, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125332, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125333 q = 1) (hb : d125654 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125333, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125333, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125334 q = 1) (hb : d125655 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125334, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125334, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125365 q = 1) (hb : d125695 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125365, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125365, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22544 q ha hb
  have h12 (q : Pattern) (ha : d125366 q = 1) (hb : d125696 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125366, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125366, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125367 q = 1) (hb : d125697 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125367, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125367, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125368 q = 1) (hb : d125698 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125368, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125368, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125369 q = 1) (hb : d125699 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125369, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125369, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125370 q = 1) (hb : d125700 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125370, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125370, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro22546 (p : Pattern) (ha : d125376 p = 1) (hb : d125706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125371 q = 1) (hb : d125701 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125371, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22545 q ha hb
    | true =>
      simp only [d125371, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125372 q = 1) (hb : d125702 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125372, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125372, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125373 q = 1) (hb : d125703 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125373, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125373, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125374 q = 1) (hb : d125704 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125374, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125374, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125375 q = 1) (hb : d125705 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125375, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125375, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125376 q = 1) (hb : d125706 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125376, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125376, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22547 (p : Pattern) (ha : d125382 p = 1) (hb : d125712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125377 q = 1) (hb : d125707 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125377, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22546 q ha hb
    | true =>
      simp only [d125377, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125378 q = 1) (hb : d125708 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125378, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125378, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125379 q = 1) (hb : d125709 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125379, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125379, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125380 q = 1) (hb : d125710 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125380, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125380, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125381 q = 1) (hb : d125711 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125381, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125381, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125382 q = 1) (hb : d125712 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125382, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125382, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22548 (p : Pattern) (ha : d125388 p = 1) (hb : d125718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125383 q = 1) (hb : d125713 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125383, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22547 q ha hb
    | true =>
      simp only [d125383, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125384 q = 1) (hb : d125714 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125384, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125384, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125385 q = 1) (hb : d125715 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125385, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125385, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125386 q = 1) (hb : d125716 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125386, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125386, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125387 q = 1) (hb : d125717 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125387, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125387, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125388 q = 1) (hb : d125718 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125388, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125388, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22549 (p : Pattern) (ha : d125394 p = 1) (hb : d125724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125389 q = 1) (hb : d125719 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125389, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22548 q ha hb
    | true =>
      simp only [d125389, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125390 q = 1) (hb : d125720 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125390, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125390, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125391 q = 1) (hb : d125721 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125391, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125391, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125392 q = 1) (hb : d125722 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125392, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125392, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125393 q = 1) (hb : d125723 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125393, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125393, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125394 q = 1) (hb : d125724 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125394, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125394, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22550 (p : Pattern) (ha : d125400 p = 1) (hb : d125730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125395 q = 1) (hb : d125725 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125395, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22549 q ha hb
    | true =>
      simp only [d125395, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125396 q = 1) (hb : d125726 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125396, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125396, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125397 q = 1) (hb : d125727 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125397, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125397, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125398 q = 1) (hb : d125728 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125398, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125398, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125399 q = 1) (hb : d125729 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125399, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125399, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125400 q = 1) (hb : d125730 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125400, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125400, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22551 (p : Pattern) (ha : d125406 p = 1) (hb : d125736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125401 q = 1) (hb : d125731 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125401, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22550 q ha hb
    | true =>
      simp only [d125401, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125402 q = 1) (hb : d125732 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125402, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125402, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125403 q = 1) (hb : d125733 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125403, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125403, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125404 q = 1) (hb : d125734 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125404, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125404, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125405 q = 1) (hb : d125735 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125405, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125405, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125406 q = 1) (hb : d125736 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125406, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125406, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22552 (p : Pattern) (ha : d125412 p = 1) (hb : d125742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125407 q = 1) (hb : d125737 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125407, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22551 q ha hb
    | true =>
      simp only [d125407, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125408 q = 1) (hb : d125738 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125408, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125408, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125409 q = 1) (hb : d125739 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125409, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125409, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125410 q = 1) (hb : d125740 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125410, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125410, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125411 q = 1) (hb : d125741 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125411, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125411, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125412 q = 1) (hb : d125742 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125412, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125412, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22553 (p : Pattern) (ha : d6739 p = 1) (hb : d125748 p = 1) : d125750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d475 q = 1) (hb : d125746 q = 1) : d10863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d475, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d125747 q = 1) : d34 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6738 q = 1) (hb : d125748 q = 1) : d125749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d125748, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6738, d125748, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6739 q = 1) (hb : d125748 q = 1) : d125750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6739, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22554 (p : Pattern) (ha : d8238 p = 1) (hb : d125748 p = 1) : d125756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d125748 q = 1) : d125755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8238 q = 1) (hb : d125748 q = 1) : d125756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22555 (p : Pattern) (ha : d94191 p = 1) (hb : d125748 p = 1) : d125762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d125748 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d125748 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
    | true =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d125748 q = 1) : d125758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94187, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d125748 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d125748 q = 1) : d125759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d125748 q = 1) : d125760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94189, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d125748 q = 1) : d125761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94190, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94191 q = 1) (hb : d125748 q = 1) : d125762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94191, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22556 (p : Pattern) (ha : d8245 p = 1) (hb : d125748 p = 1) : d125763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d125748 q = 1) : d125755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8245 q = 1) (hb : d125748 q = 1) : d125763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8245, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro22557 (p : Pattern) (ha : d94196 p = 1) (hb : d125748 p = 1) : d125769 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d125748 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d125748 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
    | true =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d125748 q = 1) : d125758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94187, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d125748 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d125748 q = 1) : d125759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d125748 q = 1) : d125760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94189, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d125748 q = 1) : d125761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94190, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d125748 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d125748 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8246 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22556 q ha hb
    | true =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94192 q = 1) (hb : d125748 q = 1) : d125765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94192, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d125748 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d94193 q = 1) (hb : d125748 q = 1) : d125766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94193, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94194 q = 1) (hb : d125748 q = 1) : d125767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94194, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94195 q = 1) (hb : d125748 q = 1) : d125768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94195, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d94196 q = 1) (hb : d125748 q = 1) : d125769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94196, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22558 (p : Pattern) (ha : d94203 p = 1) (hb : d125748 p = 1) : d125776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22556 q ha hb
    | true =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94192 q = 1) (hb : d125748 q = 1) : d125765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94192, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d125748 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94193 q = 1) (hb : d125748 q = 1) : d125766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94193, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94201 q = 1) (hb : d125748 q = 1) : d125774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94201, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94202 q = 1) (hb : d125748 q = 1) : d125775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94202, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94203 q = 1) (hb : d125748 q = 1) : d125776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94203, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22559 (p : Pattern) (ha : d6772 p = 1) (hb : d125748 p = 1) : d125783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d673 q = 1) (hb : d125746 q = 1) : d11021 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d673, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d125747 q = 1) : d75 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6771 q = 1) (hb : d125748 q = 1) : d125782 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d125748, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6771, d125748, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6772 q = 1) (hb : d125748 q = 1) : d125783 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6772, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22560 (p : Pattern) (ha : d8267 p = 1) (hb : d125748 p = 1) : d125789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22559 q ha hb
    | true =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d125748 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8264 q = 1) (hb : d125748 q = 1) : d125786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8265 q = 1) (hb : d125748 q = 1) : d125787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8265, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8266 q = 1) (hb : d125748 q = 1) : d125788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8266, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8267 q = 1) (hb : d125748 q = 1) : d125789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8267, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro22561 (p : Pattern) (ha : d94213 p = 1) (hb : d125748 p = 1) : d125795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d125748 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d125748 q = 1) : d125790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22560 q ha hb
    | true =>
      simp only [d8268, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94209 q = 1) (hb : d125748 q = 1) : d125791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94209, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d125748 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94210 q = 1) (hb : d125748 q = 1) : d125792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94210, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94211 q = 1) (hb : d125748 q = 1) : d125793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94211, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94212 q = 1) (hb : d125748 q = 1) : d125794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94212, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94213 q = 1) (hb : d125748 q = 1) : d125795 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94213, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22562 (p : Pattern) (ha : d94219 p = 1) (hb : d125748 p = 1) : d125801 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d125748 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94197 q = 1) (hb : d125748 q = 1) : d125770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22555 q ha hb
    | true =>
      simp only [d94197, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22557 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d125748 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94198 q = 1) (hb : d125748 q = 1) : d125771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94198, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94199 q = 1) (hb : d125748 q = 1) : d125772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94199, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94200 q = 1) (hb : d125748 q = 1) : d125773 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94200, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94204 q = 1) (hb : d125748 q = 1) : d125777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94204, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22558 q ha hb
  have h8 (q : Pattern) (ha : d94205 q = 1) (hb : d125748 q = 1) : d125778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94205, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d94206 q = 1) (hb : d125748 q = 1) : d125779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94206, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d94207 q = 1) (hb : d125748 q = 1) : d125780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94207, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94208 q = 1) (hb : d125748 q = 1) : d125781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94208, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94214 q = 1) (hb : d125748 q = 1) : d125796 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94214, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22561 q ha hb
  have h13 (q : Pattern) (ha : d94215 q = 1) (hb : d125748 q = 1) : d125797 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94215, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d94216 q = 1) (hb : d125748 q = 1) : d125798 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94216, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d94217 q = 1) (hb : d125748 q = 1) : d125799 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94217, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d94218 q = 1) (hb : d125748 q = 1) : d125800 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94218, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94219 q = 1) (hb : d125748 q = 1) : d125801 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94219, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22563 (p : Pattern) (ha : d8289 p = 1) (hb : d125748 p = 1) : d125811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
    | true =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8289 q = 1) (hb : d125748 q = 1) : d125811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22564 (p : Pattern) (ha : d8296 p = 1) (hb : d125748 p = 1) : d125818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
    | true =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8246 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22556 q ha hb
    | true =>
      simp only [d8246, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8292 q = 1) (hb : d125748 q = 1) : d125814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8293 q = 1) (hb : d125748 q = 1) : d125815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8293, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8294 q = 1) (hb : d125748 q = 1) : d125816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8295 q = 1) (hb : d125748 q = 1) : d125817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8296 q = 1) (hb : d125748 q = 1) : d125818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8296, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22565 (p : Pattern) (ha : d8363 p = 1) (hb : d125748 p = 1) : d125875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
    | true =>
      simp only [d8239, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d125748 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8363 q = 1) (hb : d125748 q = 1) : d125875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d125875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8363, d125875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22566 (p : Pattern) (ha : d8301 p = 1) (hb : d125748 p = 1) : d125823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d125748 q = 1) : d125822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8301 q = 1) (hb : d125748 q = 1) : d125823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22567 (p : Pattern) (ha : d8308 p = 1) (hb : d125748 p = 1) : d125830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d125748 q = 1) : d125828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d125748 q = 1) : d125829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8308 q = 1) (hb : d125748 q = 1) : d125830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22568 (p : Pattern) (ha : d8313 p = 1) (hb : d125748 p = 1) : d125836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d324 q = 1) : d324 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d325 q = 1) (hb : d85721 q = 1) : d10742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d326 q = 1) (hb : d85721 q = 1) : d10743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d327 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6797 q = 1) (hb : d125746 q = 1) : d125834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6797, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d145 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d145, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d146 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d475 q = 1) (hb : d125747 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d475, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8312 q = 1) (hb : d125748 q = 1) : d125835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8312, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8313 q = 1) (hb : d125748 q = 1) : d125836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8313, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22569 (p : Pattern) (ha : d8319 p = 1) (hb : d125748 p = 1) : d125842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d125748 q = 1) : d125839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d125748 q = 1) : d125840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d125748 q = 1) : d125841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d125748 q = 1) : d125842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22570 (p : Pattern) (ha : d8334 p = 1) (hb : d125748 p = 1) : d125848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d125748 q = 1) : d125845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d125748 q = 1) : d125846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d125748 q = 1) : d125847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d125748 q = 1) : d125848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22571 (p : Pattern) (ha : d94229 p = 1) (hb : d125748 p = 1) : d125854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d125748 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d125748 q = 1) : d125824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22566 q ha hb
    | true =>
      simp only [d8302, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d125748 q = 1) : d125825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d125748 q = 1) : d125826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d125748 q = 1) : d125827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d125748 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d125748 q = 1) : d125831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22567 q ha hb
    | true =>
      simp only [d8309, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d125748 q = 1) : d125832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d125748 q = 1) : d125833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d125748 q = 1) : d125843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22569 q ha hb
    | true =>
      simp only [d8320, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d125748 q = 1) : d125844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d125748 q = 1) : d125849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22570 q ha hb
    | true =>
      simp only [d8335, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d125748 q = 1) : d125850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d125748 q = 1) : d125851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d125748 q = 1) : d125852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d125748 q = 1) : d125853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94229 q = 1) (hb : d125748 q = 1) : d125854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22572 (p : Pattern) (ha : d8341 p = 1) (hb : d125748 p = 1) : d125855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d125748 q = 1) : d125822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8341 q = 1) (hb : d125748 q = 1) : d125855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8341, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro22573 (p : Pattern) (ha : d8346 p = 1) (hb : d125748 p = 1) : d125860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d125748 q = 1) : d125828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d125748 q = 1) : d125829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8346 q = 1) (hb : d125748 q = 1) : d125860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8346, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro22574 (p : Pattern) (ha : d8350 p = 1) (hb : d125748 p = 1) : d125864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d125748 q = 1) : d125839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d125748 q = 1) : d125840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d125748 q = 1) : d125841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d125748 q = 1) : d125864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22575 (p : Pattern) (ha : d8355 p = 1) (hb : d125748 p = 1) : d125867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22553 q ha hb
    | true =>
      simp only [d6740, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d125748 q = 1) : d125845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d125748 q = 1) : d125846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d125748 q = 1) : d125847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d125748 q = 1) : d125867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22576 (p : Pattern) (ha : d94234 p = 1) (hb : d125748 p = 1) : d125873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d125748 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d125748 q = 1) : d125824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22566 q ha hb
    | true =>
      simp only [d8302, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d125748 q = 1) : d125825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d125748 q = 1) : d125826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d125748 q = 1) : d125827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d125748 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d125748 q = 1) : d125831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22567 q ha hb
    | true =>
      simp only [d8309, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d125748 q = 1) : d125832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d125748 q = 1) : d125833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d125748 q = 1) : d125843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22569 q ha hb
    | true =>
      simp only [d8320, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22554 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d125748 q = 1) : d125844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d125748 q = 1) : d125849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22570 q ha hb
    | true =>
      simp only [d8335, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d125748 q = 1) : d125850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d125748 q = 1) : d125851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d125748 q = 1) : d125852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d125748 q = 1) : d125853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d125748 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8342 q = 1) (hb : d125748 q = 1) : d125856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22572 q ha hb
    | true =>
      simp only [d8342, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8343 q = 1) (hb : d125748 q = 1) : d125857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8344 q = 1) (hb : d125748 q = 1) : d125858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8344, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8345 q = 1) (hb : d125748 q = 1) : d125859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d125748 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8347 q = 1) (hb : d125748 q = 1) : d125861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22573 q ha hb
    | true =>
      simp only [d8347, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8348 q = 1) (hb : d125748 q = 1) : d125862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8349 q = 1) (hb : d125748 q = 1) : d125863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8349, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8351 q = 1) (hb : d125748 q = 1) : d125865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22574 q ha hb
    | true =>
      simp only [d8351, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22556 q ha hb
  have h27 (q : Pattern) (ha : d94230 q = 1) (hb : d125748 q = 1) : d125866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94230, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d8356 q = 1) (hb : d125748 q = 1) : d125868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22575 q ha hb
    | true =>
      simp only [d8356, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8357 q = 1) (hb : d125748 q = 1) : d125869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8357, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d94231 q = 1) (hb : d125748 q = 1) : d125870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94231, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d94232 q = 1) (hb : d125748 q = 1) : d125871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d94232, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d94233 q = 1) (hb : d125748 q = 1) : d125872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94233, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d94234 q = 1) (hb : d125748 q = 1) : d125873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94234, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro22577 (p : Pattern) (ha : d94241 p = 1) (hb : d125748 p = 1) : d125882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d125748 q = 1) : d125865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22574 q ha hb
    | true =>
      simp only [d8351, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22556 q ha hb
  have h2 (q : Pattern) (ha : d94230 q = 1) (hb : d125748 q = 1) : d125866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94230, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d125748 q = 1) : d125868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22575 q ha hb
    | true =>
      simp only [d8356, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d125748 q = 1) : d125869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d125748 q = 1) : d125870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d125748 q = 1) : d125880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d125880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d125880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d125748 q = 1) : d125881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d125881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d125881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d125748 q = 1) : d125882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d125882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d125882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22578 (p : Pattern) (ha : d8377 p = 1) (hb : d125748 p = 1) : d125890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d417 q = 1) : d417 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d418 q = 1) (hb : d85721 q = 1) : d10814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d419 q = 1) (hb : d85721 q = 1) : d10815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d420 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6843 q = 1) (hb : d125746 q = 1) : d125888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6843, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d232 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d232, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d233 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d233, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d234 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d234, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d673 q = 1) (hb : d125747 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d673, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8376 q = 1) (hb : d125748 q = 1) : d125889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8376, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8377 q = 1) (hb : d125748 q = 1) : d125890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8377, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22579 (p : Pattern) (ha : d8383 p = 1) (hb : d125748 p = 1) : d125896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22578 q ha hb
    | true =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22559 q ha hb
    | true =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d125748 q = 1) : d125893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d125893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d125893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d125748 q = 1) : d125894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d125894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d125894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d125748 q = 1) : d125895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d125895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d125895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d125748 q = 1) : d125896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d125896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d125896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22580 (p : Pattern) (ha : d8398 p = 1) (hb : d125748 p = 1) : d125902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22559 q ha hb
    | true =>
      simp only [d6773, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d125748 q = 1) : d125899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d125899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d125899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d125748 q = 1) : d125900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d125900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d125900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d125748 q = 1) : d125901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d125901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d125901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d125748 q = 1) : d125902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d125902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d125902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22581 (p : Pattern) (ha : d94251 p = 1) (hb : d125748 p = 1) : d125908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d125748 q = 1) : d125897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d125897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22579 q ha hb
    | true =>
      simp only [d8384, d125897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22560 q ha hb
  have h2 (q : Pattern) (ha : d94247 q = 1) (hb : d125748 q = 1) : d125898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d125898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94247, d125898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d125748 q = 1) : d125903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d125903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22580 q ha hb
    | true =>
      simp only [d8399, d125903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d125748 q = 1) : d125904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d125904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d125904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d125748 q = 1) : d125905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d125905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d125905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d125748 q = 1) : d125906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d125906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d125906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d125748 q = 1) : d125907 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d125907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d125907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d125748 q = 1) : d125908 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d125908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d125908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22582 (p : Pattern) (ha : d94257 p = 1) (hb : d125748 p = 1) : d125914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d125748 q = 1) : d125812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d125812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d125812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22563 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d125748 q = 1) : d125813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d125813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d125813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d125748 q = 1) : d125819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22563 q ha hb
    | true =>
      simp only [d8297, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22564 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d125748 q = 1) : d125820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d125748 q = 1) : d125821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d125821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d125821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94235 q = 1) (hb : d125748 q = 1) : d125874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d125874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22571 q ha hb
    | true =>
      simp only [d94235, d125874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22576 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d125748 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8364 q = 1) (hb : d125748 q = 1) : d125876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d125876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22565 q ha hb
    | true =>
      simp only [d8364, d125876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94236 q = 1) (hb : d125748 q = 1) : d125877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d125877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d125877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94237 q = 1) (hb : d125748 q = 1) : d125878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d125878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94237, d125878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d94238 q = 1) (hb : d125748 q = 1) : d125879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d125879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94238, d125879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94242 q = 1) (hb : d125748 q = 1) : d125883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d125883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94242, d125883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22577 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d125748 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d94243 q = 1) (hb : d125748 q = 1) : d125884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d125884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94243, d125884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94244 q = 1) (hb : d125748 q = 1) : d125885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d125885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94244, d125885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94245 q = 1) (hb : d125748 q = 1) : d125886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d125886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94245, d125886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d94246 q = 1) (hb : d125748 q = 1) : d125887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d125887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94246, d125887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94252 q = 1) (hb : d125748 q = 1) : d125909 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d125909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94252, d125909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22581 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d125748 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d94253 q = 1) (hb : d125748 q = 1) : d125910 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d125910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94253, d125910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d94254 q = 1) (hb : d125748 q = 1) : d125911 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d125911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94254, d125911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94255 q = 1) (hb : d125748 q = 1) : d125912 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d125912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94255, d125912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94256 q = 1) (hb : d125748 q = 1) : d125913 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d125913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94256, d125913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d94257 q = 1) (hb : d125748 q = 1) : d125914 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d125914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94257, d125914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro22583 (p : Pattern) (ha : d94263 p = 1) (hb : d125748 p = 1) : d125920 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d125748 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94220 q = 1) (hb : d125748 q = 1) : d125802 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d125802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94220, d125802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22562 q ha hb
  have h3 (q : Pattern) (ha : d94221 q = 1) (hb : d125748 q = 1) : d125803 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d125803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94221, d125803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94222 q = 1) (hb : d125748 q = 1) : d125804 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d125804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94222, d125804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94223 q = 1) (hb : d125748 q = 1) : d125805 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d125805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94223, d125805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94224 q = 1) (hb : d125748 q = 1) : d125806 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d125806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94224, d125806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d125748 q = 1) : d125915 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d125915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d125915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22582 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d125748 q = 1) : d125916 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d125916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d125916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d125748 q = 1) : d125917 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d125917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d125917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d125748 q = 1) : d125918 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d125918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d125918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d125748 q = 1) : d125919 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d125919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d125919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d125748 q = 1) : d125920 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d125920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94263, d125920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22584 (p : Pattern) (ha : d481 p = 1) (hb : d125748 p = 1) : d10869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d144 q = 1) : d144 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d85721 q = 1) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d85721, d10649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d85721 q = 1) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d10650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d10651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d475 q = 1) (hb : d125746 q = 1) : d10863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d475, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d480 q = 1) (hb : d125748 q = 1) : d10868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d125748, d10868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d480, d125748, d10868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d481 q = 1) (hb : d125748 q = 1) : d10869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d481, d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22585 (p : Pattern) (ha : d491 p = 1) (hb : d125748 p = 1) : d10879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d125748 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d125748 q = 1) : d10878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d125748 q = 1) : d10879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22586 (p : Pattern) (ha : d501 p = 1) (hb : d125748 p = 1) : d10889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d125748 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d125748 q = 1) : d10878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d125748 q = 1) : d10889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22587 (p : Pattern) (ha : d644 p = 1) (hb : d125748 p = 1) : d10998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d125748 q = 1) : d10987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22585 q ha hb
    | true =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d125748 q = 1) : d10988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d125748 q = 1) : d10989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d125748 q = 1) : d10990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d125748 q = 1) : d10991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d125748 q = 1) : d10993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22586 q ha hb
    | true =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d125748 q = 1) : d10994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d125748 q = 1) : d10995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d125748 q = 1) : d10996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d125748 q = 1) : d10997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d125748 q = 1) : d10998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22588 (p : Pattern) (ha : d653 p = 1) (hb : d125748 p = 1) : d11007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d125748 q = 1) : d10993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22586 q ha hb
    | true =>
      simp only [d639, d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d125748 q = 1) : d10994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d125748 q = 1) : d10995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d125748 q = 1) : d10996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d125748 q = 1) : d10997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d125748 q = 1) : d11007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22589 (p : Pattern) (ha : d683 p = 1) (hb : d125748 p = 1) : d11031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d231 q = 1) : d231 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d85721 q = 1) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d85721, d10686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d85721 q = 1) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d10687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d10688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d673 q = 1) (hb : d125746 q = 1) : d11021 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d673, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d682 q = 1) (hb : d125748 q = 1) : d11030 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d125748, d11030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d682, d125748, d11030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d683 q = 1) (hb : d125748 q = 1) : d11031 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d683, d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22590 (p : Pattern) (ha : d730 p = 1) (hb : d125748 p = 1) : d11076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d125748 q = 1) : d11032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22589 q ha hb
    | true =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d125748 q = 1) : d11033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d125748 q = 1) : d11073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d11073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d11073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d125748 q = 1) : d11074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d125748 q = 1) : d11075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d125748 q = 1) : d11076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22591 (p : Pattern) (ha : d736 p = 1) (hb : d125748 p = 1) : d11082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d125748 q = 1) : d11077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22590 q ha hb
    | true =>
      simp only [d731, d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d125748 q = 1) : d11078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d125748 q = 1) : d11079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d125748 q = 1) : d11080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d125748 q = 1) : d11081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d125748 q = 1) : d11082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22592 (p : Pattern) (ha : d8420 p = 1) (hb : d125748 p = 1) : d125924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8420 q = 1) (hb : d125748 q = 1) : d125924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22593 (p : Pattern) (ha : d8426 p = 1) (hb : d125748 p = 1) : d125930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22592 q ha hb
    | true =>
      simp only [d8421, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22585 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8426 q = 1) (hb : d125748 q = 1) : d125930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22594 (p : Pattern) (ha : d8429 p = 1) (hb : d125748 p = 1) : d125933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8429 q = 1) (hb : d125748 q = 1) : d125933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8429, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22595 (p : Pattern) (ha : d8435 p = 1) (hb : d125748 p = 1) : d125939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22592 q ha hb
    | true =>
      simp only [d8421, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22585 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8430 q = 1) (hb : d125748 q = 1) : d125934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22594 q ha hb
    | true =>
      simp only [d8430, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22586 q ha hb
  have h7 (q : Pattern) (ha : d8431 q = 1) (hb : d125748 q = 1) : d125935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8432 q = 1) (hb : d125748 q = 1) : d125936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8432, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8433 q = 1) (hb : d125748 q = 1) : d125937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8434 q = 1) (hb : d125748 q = 1) : d125938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8435 q = 1) (hb : d125748 q = 1) : d125939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8435, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22596 (p : Pattern) (ha : d6799 p = 1) (hb : d125748 p = 1) : d125836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d324 q = 1) : d324 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d325 q = 1) (hb : d85721 q = 1) : d10742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d325, d85721, d10742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d326 q = 1) (hb : d85721 q = 1) : d10743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d10743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d327 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d10744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6797 q = 1) (hb : d125746 q = 1) : d125834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6797, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d4818 q = 1) (hb : d94753 q = 1) : d4818 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4819 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4819, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4820 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4820, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4821 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4821, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4822 q = 1) (hb : d125747 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4822, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d6798 q = 1) (hb : d125748 q = 1) : d125835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6798, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6799 q = 1) (hb : d125748 q = 1) : d125836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d6799, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22597 (p : Pattern) (ha : d8463 p = 1) (hb : d125748 p = 1) : d125924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22596 q ha hb
    | true =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8463 q = 1) (hb : d125748 q = 1) : d125924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22598 (p : Pattern) (ha : d8514 p = 1) (hb : d125748 p = 1) : d125997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8509 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22597 q ha hb
    | true =>
      simp only [d8509, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22585 q ha hb
  have h2 (q : Pattern) (ha : d8510 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8511 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8511, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8512 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8513 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d125748 q = 1) : d10987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22585 q ha hb
    | true =>
      simp only [d633, d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d125748 q = 1) : d10988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d125748 q = 1) : d10989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d125748 q = 1) : d10990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d125748 q = 1) : d10991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8514 q = 1) (hb : d125748 q = 1) : d125997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d125997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8514, d125997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22599 (p : Pattern) (ha : d514 p = 1) (hb : d125748 p = 1) : d10902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d125748 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d125748 q = 1) : d10901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d125748 q = 1) : d10902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22600 (p : Pattern) (ha : d524 p = 1) (hb : d125748 p = 1) : d10912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d125748 q = 1) : d10910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d125748 q = 1) : d10911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d125748 q = 1) : d10912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22601 (p : Pattern) (ha : d8440 p = 1) (hb : d125748 p = 1) : d125944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d125748 q = 1) : d125943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8440 q = 1) (hb : d125748 q = 1) : d125944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8440, d125944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8440, d125944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22602 (p : Pattern) (ha : d8447 p = 1) (hb : d125748 p = 1) : d125951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d125748 q = 1) : d125949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d125748 q = 1) : d125950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8447 q = 1) (hb : d125748 q = 1) : d125951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8447, d125951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8447, d125951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22603 (p : Pattern) (ha : d8453 p = 1) (hb : d125748 p = 1) : d125958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d548 q = 1) : d548 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d549 q = 1) (hb : d85721 q = 1) : d10916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d85721, d10916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d549, d85721, d10916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d550 q = 1) (hb : d85721 q = 1) : d10917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d10917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d10917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d551 q = 1) (hb : d85721 q = 1) : d10918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d10918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d10918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8451 q = 1) (hb : d125746 q = 1) : d125955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d125746, d125955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8451, d125746, d125955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d325 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d325, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d326 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d326, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d327 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d327, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6797 q = 1) (hb : d125747 q = 1) : d125956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d125747, d125956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6797, d125747, d125956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8452 q = 1) (hb : d125748 q = 1) : d125957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8452, d125748, d125957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8452, d125748, d125957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8453 q = 1) (hb : d125748 q = 1) : d125958 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8453, d125958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8453, d125958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22604 (p : Pattern) (ha : d8459 p = 1) (hb : d125748 p = 1) : d125964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d125748 q = 1) : d125959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22603 q ha hb
    | true =>
      simp only [d8454, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d125748 q = 1) : d125960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22596 q ha hb
    | true =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d125748 q = 1) : d125961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d125748 q = 1) : d125962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d125748 q = 1) : d125963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8459 q = 1) (hb : d125748 q = 1) : d125964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8459, d125964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8459, d125964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22605 (p : Pattern) (ha : d8479 p = 1) (hb : d125748 p = 1) : d125970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d125748 q = 1) : d125967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d125748 q = 1) : d125968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d125748 q = 1) : d125969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d125748 q = 1) : d125970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d125970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d125970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22606 (p : Pattern) (ha : d94268 p = 1) (hb : d125748 p = 1) : d125976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d125748 q = 1) : d125945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22601 q ha hb
    | true =>
      simp only [d8441, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22599 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d125748 q = 1) : d125946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d125748 q = 1) : d125947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d125748 q = 1) : d125948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d125748 q = 1) : d125952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22602 q ha hb
    | true =>
      simp only [d8448, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22600 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d125748 q = 1) : d125953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d125748 q = 1) : d125954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d125748 q = 1) : d125965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22604 q ha hb
    | true =>
      simp only [d8464, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22597 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d125748 q = 1) : d125966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d125748 q = 1) : d125971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22605 q ha hb
    | true =>
      simp only [d8480, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d125748 q = 1) : d125972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d125748 q = 1) : d125973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d125748 q = 1) : d125974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d125748 q = 1) : d125975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94268 q = 1) (hb : d125748 q = 1) : d125976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d125976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d125976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22607 (p : Pattern) (ha : d610 p = 1) (hb : d125748 p = 1) : d10963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d125748 q = 1) : d10877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d125748 q = 1) : d10901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d125748 q = 1) : d10963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22608 (p : Pattern) (ha : d616 p = 1) (hb : d125748 p = 1) : d10969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d125748 q = 1) : d10876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d10876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d125748 q = 1) : d10910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d125748 q = 1) : d10911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d125748 q = 1) : d10969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22609 (p : Pattern) (ha : d8486 p = 1) (hb : d125748 p = 1) : d125977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d125748 q = 1) : d125943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8486 q = 1) (hb : d125748 q = 1) : d125977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, d125977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8486, d125977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22610 (p : Pattern) (ha : d8491 p = 1) (hb : d125748 p = 1) : d125982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d125748 q = 1) : d125949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d125748 q = 1) : d125950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8491 q = 1) (hb : d125748 q = 1) : d125982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, d125982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8491, d125982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22611 (p : Pattern) (ha : d8495 p = 1) (hb : d125748 p = 1) : d125986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d125748 q = 1) : d125959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22603 q ha hb
    | true =>
      simp only [d8454, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d125748 q = 1) : d125960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22596 q ha hb
    | true =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d125748 q = 1) : d125961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d125748 q = 1) : d125962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d125748 q = 1) : d125963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8495 q = 1) (hb : d125748 q = 1) : d125986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, d125986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8495, d125986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22612 (p : Pattern) (ha : d8496 p = 1) (hb : d125748 p = 1) : d125933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22596 q ha hb
    | true =>
      simp only [d6800, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d125748 q = 1) : d10870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22584 q ha hb
    | true =>
      simp only [d482, d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8496 q = 1) (hb : d125748 q = 1) : d125933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8496, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22613 (p : Pattern) (ha : d8501 p = 1) (hb : d125748 p = 1) : d125989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22568 q ha hb
    | true =>
      simp only [d8314, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d125748 q = 1) : d125967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d125748 q = 1) : d125968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d125748 q = 1) : d125969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d125748 q = 1) : d125989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d125989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d125989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22614 (p : Pattern) (ha : d94273 p = 1) (hb : d125748 p = 1) : d125995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d125748 q = 1) : d125945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22601 q ha hb
    | true =>
      simp only [d8441, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22599 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d125748 q = 1) : d125946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d125748 q = 1) : d125947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d125748 q = 1) : d125948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d125748 q = 1) : d125952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22602 q ha hb
    | true =>
      simp only [d8448, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22600 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d125748 q = 1) : d125953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d125748 q = 1) : d125954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d125748 q = 1) : d125965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22604 q ha hb
    | true =>
      simp only [d8464, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22597 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d125748 q = 1) : d125966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d125748 q = 1) : d125971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22605 q ha hb
    | true =>
      simp only [d8480, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d125748 q = 1) : d125972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d125748 q = 1) : d125973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d125748 q = 1) : d125974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d125748 q = 1) : d125975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8487 q = 1) (hb : d125748 q = 1) : d125978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, d125978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22609 q ha hb
    | true =>
      simp only [d8487, d125978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22607 q ha hb
  have h16 (q : Pattern) (ha : d8488 q = 1) (hb : d125748 q = 1) : d125979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, d125979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, d125979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8489 q = 1) (hb : d125748 q = 1) : d125980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, d125980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8489, d125980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8490 q = 1) (hb : d125748 q = 1) : d125981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, d125981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, d125981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8492 q = 1) (hb : d125748 q = 1) : d125983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, d125983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22610 q ha hb
    | true =>
      simp only [d8492, d125983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22608 q ha hb
  have h20 (q : Pattern) (ha : d8493 q = 1) (hb : d125748 q = 1) : d125984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, d125984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, d125984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8494 q = 1) (hb : d125748 q = 1) : d125985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, d125985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8494, d125985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8497 q = 1) (hb : d125748 q = 1) : d125987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22611 q ha hb
    | true =>
      simp only [d8497, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22612 q ha hb
  have h23 (q : Pattern) (ha : d94269 q = 1) (hb : d125748 q = 1) : d125988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94269, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8502 q = 1) (hb : d125748 q = 1) : d125990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22613 q ha hb
    | true =>
      simp only [d8502, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8503 q = 1) (hb : d125748 q = 1) : d125991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8503, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94270 q = 1) (hb : d125748 q = 1) : d125992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94270, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94271 q = 1) (hb : d125748 q = 1) : d125993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d125993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94271, d125993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94272 q = 1) (hb : d125748 q = 1) : d125994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d125994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94272, d125994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94273 q = 1) (hb : d125748 q = 1) : d125995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d125995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94273, d125995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22615 (p : Pattern) (ha : d94280 p = 1) (hb : d125748 p = 1) : d126004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d125748 q = 1) : d125987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22611 q ha hb
    | true =>
      simp only [d8497, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22612 q ha hb
  have h2 (q : Pattern) (ha : d94269 q = 1) (hb : d125748 q = 1) : d125988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94269, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8502 q = 1) (hb : d125748 q = 1) : d125990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22613 q ha hb
    | true =>
      simp only [d8502, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8503 q = 1) (hb : d125748 q = 1) : d125991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8503, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d125748 q = 1) : d125992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d125748 q = 1) : d126002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d126002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d126002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d125748 q = 1) : d126003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d126003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d126003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d125748 q = 1) : d126004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d126004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d126004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22616 (p : Pattern) (ha : d6845 p = 1) (hb : d125748 p = 1) : d125890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d417 q = 1) : d417 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d418 q = 1) (hb : d85721 q = 1) : d10814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d418, d85721, d10814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d419 q = 1) (hb : d85721 q = 1) : d10815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d10815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d420 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d10816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6843 q = 1) (hb : d125746 q = 1) : d125888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6843, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6078 q = 1) (hb : d94753 q = 1) : d6078 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6079 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6079, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d6080 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6080, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6081 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6081, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6082 q = 1) (hb : d125747 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6082, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d6844 q = 1) (hb : d125748 q = 1) : d125889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6844, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6844, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6845 q = 1) (hb : d125748 q = 1) : d125890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6845, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d6845, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22617 (p : Pattern) (ha : d8529 p = 1) (hb : d125748 p = 1) : d126013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d664 q = 1) : d664 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d665 q = 1) (hb : d85721 q = 1) : d11013 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d85721, d11013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d665, d85721, d11013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d666 q = 1) (hb : d85721 q = 1) : d11014 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d11014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d11014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d667 q = 1) (hb : d85721 q = 1) : d11015 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d11015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d11015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8527 q = 1) (hb : d125746 q = 1) : d126010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d125746, d126010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8527, d125746, d126010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d418 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d418, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d419 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d419, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d420 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d420, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6843 q = 1) (hb : d125747 q = 1) : d126011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d125747, d126011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6843, d125747, d126011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8528 q = 1) (hb : d125748 q = 1) : d126012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8528, d125748, d126012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8528, d125748, d126012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8529 q = 1) (hb : d125748 q = 1) : d126013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8529, d126013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8529, d126013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22618 (p : Pattern) (ha : d8535 p = 1) (hb : d125748 p = 1) : d126019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d125748 q = 1) : d126014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d126014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22617 q ha hb
    | true =>
      simp only [d8530, d126014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d125748 q = 1) : d126015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d126015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d126015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6846 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22616 q ha hb
    | true =>
      simp only [d6846, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6847 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8532 q = 1) (hb : d125748 q = 1) : d126016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, d126016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8532, d126016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8533 q = 1) (hb : d125748 q = 1) : d126017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, d126017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8533, d126017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8534 q = 1) (hb : d125748 q = 1) : d126018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, d126018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8534, d126018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8535 q = 1) (hb : d125748 q = 1) : d126019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, d126019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8535, d126019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22619 (p : Pattern) (ha : d8539 p = 1) (hb : d125748 p = 1) : d126023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22616 q ha hb
    | true =>
      simp only [d6846, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d125748 q = 1) : d11032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22589 q ha hb
    | true =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d125748 q = 1) : d11033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8536 q = 1) (hb : d125748 q = 1) : d126020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8536, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8537 q = 1) (hb : d125748 q = 1) : d126021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8537, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8538 q = 1) (hb : d125748 q = 1) : d126022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8538, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8539 q = 1) (hb : d125748 q = 1) : d126023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8539, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22620 (p : Pattern) (ha : d8555 p = 1) (hb : d125748 p = 1) : d126029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22578 q ha hb
    | true =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d125748 q = 1) : d126026 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d126026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d126026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d125748 q = 1) : d126027 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d126027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d126027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d125748 q = 1) : d126028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d126028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d126028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d125748 q = 1) : d126029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d126029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d126029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22621 (p : Pattern) (ha : d94290 p = 1) (hb : d125748 p = 1) : d126035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d125748 q = 1) : d126024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, d126024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22618 q ha hb
    | true =>
      simp only [d8540, d126024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22619 q ha hb
  have h2 (q : Pattern) (ha : d94286 q = 1) (hb : d125748 q = 1) : d126025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d126025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94286, d126025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8556 q = 1) (hb : d125748 q = 1) : d126030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d126030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22620 q ha hb
    | true =>
      simp only [d8556, d126030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8557 q = 1) (hb : d125748 q = 1) : d126031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d126031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8557, d126031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d125748 q = 1) : d126032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d126032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, d126032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d125748 q = 1) : d126033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d126033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d126033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d125748 q = 1) : d126034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d126034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d126034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d125748 q = 1) : d126035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d126035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d126035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22622 (p : Pattern) (ha : d94296 p = 1) (hb : d125748 p = 1) : d126041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d125748 q = 1) : d125931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, d125931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, d125931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22593 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d125748 q = 1) : d125932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, d125932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, d125932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d125748 q = 1) : d125940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22593 q ha hb
    | true =>
      simp only [d8436, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22595 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d125748 q = 1) : d125941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d125748 q = 1) : d125942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, d125942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, d125942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94274 q = 1) (hb : d125748 q = 1) : d125996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d125996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22606 q ha hb
    | true =>
      simp only [d94274, d125996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22614 q ha hb
  have h7 (q : Pattern) (ha : d8515 q = 1) (hb : d125748 q = 1) : d125998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, d125998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22598 q ha hb
    | true =>
      simp only [d8515, d125998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22587 q ha hb
  have h8 (q : Pattern) (ha : d94275 q = 1) (hb : d125748 q = 1) : d125999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d125999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, d125999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94276 q = 1) (hb : d125748 q = 1) : d126000 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d126000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94276, d126000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94277 q = 1) (hb : d125748 q = 1) : d126001 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d126001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94277, d126001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94281 q = 1) (hb : d125748 q = 1) : d126005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d126005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94281, d126005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22615 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d125748 q = 1) : d11008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22588 q ha hb
  have h13 (q : Pattern) (ha : d94282 q = 1) (hb : d125748 q = 1) : d126006 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d126006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94282, d126006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94283 q = 1) (hb : d125748 q = 1) : d126007 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d126007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94283, d126007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94284 q = 1) (hb : d125748 q = 1) : d126008 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d126008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94284, d126008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94285 q = 1) (hb : d125748 q = 1) : d126009 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d126009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94285, d126009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94291 q = 1) (hb : d125748 q = 1) : d126036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d126036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94291, d126036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22621 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d125748 q = 1) : d11083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22591 q ha hb
  have h19 (q : Pattern) (ha : d94292 q = 1) (hb : d125748 q = 1) : d126037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d126037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94292, d126037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94293 q = 1) (hb : d125748 q = 1) : d126038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d126038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94293, d126038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94294 q = 1) (hb : d125748 q = 1) : d126039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d126039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94294, d126039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94295 q = 1) (hb : d125748 q = 1) : d126040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d126040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94295, d126040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94296 q = 1) (hb : d125748 q = 1) : d126041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d126041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94296, d126041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22623 (p : Pattern) (ha : d94302 p = 1) (hb : d125748 p = 1) : d126047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d125748 q = 1) : d126042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d126042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d126042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22622 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d125748 q = 1) : d126043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d126043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d126043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d125748 q = 1) : d126044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d126044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d126044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d125748 q = 1) : d126045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d126045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d126045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d125748 q = 1) : d126046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d126046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d126046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d125748 q = 1) : d126047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d126047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d126047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22624 (p : Pattern) (ha : d773 p = 1) (hb : d125748 p = 1) : d11109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d767 q = 1) (hb : d125746 q = 1) : d11103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d125746, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d767, d125746, d11103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d772 q = 1) (hb : d125748 q = 1) : d11108 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d125748, d11108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d772, d125748, d11108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d773 q = 1) (hb : d125748 q = 1) : d11109 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d773, d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22625 (p : Pattern) (ha : d783 p = 1) (hb : d125748 p = 1) : d11119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d125748 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d125748 q = 1) : d11118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d125748 q = 1) : d11119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22626 (p : Pattern) (ha : d793 p = 1) (hb : d125748 p = 1) : d11129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d125748 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d125748 q = 1) : d11118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d125748 q = 1) : d11129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22627 (p : Pattern) (ha : d950 p = 1) (hb : d125748 p = 1) : d11249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d125748 q = 1) : d11238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22625 q ha hb
    | true =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d125748 q = 1) : d11239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d125748 q = 1) : d11240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d125748 q = 1) : d11241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d125748 q = 1) : d11242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d125748 q = 1) : d11244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22626 q ha hb
    | true =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d125748 q = 1) : d11245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d125748 q = 1) : d11246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d125748 q = 1) : d11247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d125748 q = 1) : d11248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d125748 q = 1) : d11249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22628 (p : Pattern) (ha : d959 p = 1) (hb : d125748 p = 1) : d11258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d125748 q = 1) : d11244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22626 q ha hb
    | true =>
      simp only [d945, d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d125748 q = 1) : d11245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d125748 q = 1) : d11246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d125748 q = 1) : d11247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d125748 q = 1) : d11248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d125748 q = 1) : d11258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22629 (p : Pattern) (ha : d1005 p = 1) (hb : d125748 p = 1) : d11289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d995 q = 1) (hb : d125746 q = 1) : d11279 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d125746, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d995, d125746, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1004 q = 1) (hb : d125748 q = 1) : d11288 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d125748, d11288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1004, d125748, d11288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1005 q = 1) (hb : d125748 q = 1) : d11289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1005, d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22630 (p : Pattern) (ha : d1063 p = 1) (hb : d125748 p = 1) : d11345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d125748 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22629 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d125748 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d125748 q = 1) : d11342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d11342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d11342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d125748 q = 1) : d11343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d125748 q = 1) : d11344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d125748 q = 1) : d11345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22631 (p : Pattern) (ha : d1069 p = 1) (hb : d125748 p = 1) : d11351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d125748 q = 1) : d11346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22630 q ha hb
    | true =>
      simp only [d1064, d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d125748 q = 1) : d11347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d125748 q = 1) : d11348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d125748 q = 1) : d11349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d125748 q = 1) : d11350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d125748 q = 1) : d11351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22632 (p : Pattern) (ha : d8576 p = 1) (hb : d125748 p = 1) : d126051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6875 q = 1) (hb : d125746 q = 1) : d126049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6875, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d763 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d763, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d764 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d764, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d765 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d765, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d767 q = 1) (hb : d125747 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d767, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8575 q = 1) (hb : d125748 q = 1) : d126050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8575, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8575, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8576 q = 1) (hb : d125748 q = 1) : d126051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8576, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8576, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22633 (p : Pattern) (ha : d8582 p = 1) (hb : d125748 p = 1) : d126057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8582 q = 1) (hb : d125748 q = 1) : d126057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22634 (p : Pattern) (ha : d8588 p = 1) (hb : d125748 p = 1) : d126063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22633 q ha hb
    | true =>
      simp only [d8583, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22625 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8588 q = 1) (hb : d125748 q = 1) : d126063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22635 (p : Pattern) (ha : d8591 p = 1) (hb : d125748 p = 1) : d126066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8591 q = 1) (hb : d125748 q = 1) : d126066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8591, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22636 (p : Pattern) (ha : d8597 p = 1) (hb : d125748 p = 1) : d126072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22633 q ha hb
    | true =>
      simp only [d8583, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22625 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8592 q = 1) (hb : d125748 q = 1) : d126067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22635 q ha hb
    | true =>
      simp only [d8592, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22626 q ha hb
  have h7 (q : Pattern) (ha : d8593 q = 1) (hb : d125748 q = 1) : d126068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8594 q = 1) (hb : d125748 q = 1) : d126069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8594, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8595 q = 1) (hb : d125748 q = 1) : d126070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8596 q = 1) (hb : d125748 q = 1) : d126071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8597 q = 1) (hb : d125748 q = 1) : d126072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8597, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22637 (p : Pattern) (ha : d6877 p = 1) (hb : d125748 p = 1) : d126051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6875 q = 1) (hb : d125746 q = 1) : d126049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6875, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d4913 q = 1) (hb : d94753 q = 1) : d4913 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4914 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4914, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d4915 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4915, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4916 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4916, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4917 q = 1) (hb : d125747 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4917, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d6876 q = 1) (hb : d125748 q = 1) : d126050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6876, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6877 q = 1) (hb : d125748 q = 1) : d126051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d6877, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22638 (p : Pattern) (ha : d8625 p = 1) (hb : d125748 p = 1) : d126057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22637 q ha hb
    | true =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8625 q = 1) (hb : d125748 q = 1) : d126057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22639 (p : Pattern) (ha : d8676 p = 1) (hb : d125748 p = 1) : d126130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8671 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22638 q ha hb
    | true =>
      simp only [d8671, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22625 q ha hb
  have h2 (q : Pattern) (ha : d8672 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8673 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8673, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8674 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8675 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d125748 q = 1) : d11238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22625 q ha hb
    | true =>
      simp only [d939, d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d125748 q = 1) : d11239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d125748 q = 1) : d11240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d125748 q = 1) : d11241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d125748 q = 1) : d11242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8676 q = 1) (hb : d125748 q = 1) : d126130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, d126130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8676, d126130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22640 (p : Pattern) (ha : d806 p = 1) (hb : d125748 p = 1) : d11142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d125748 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d125748 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d125748 q = 1) : d11142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22641 (p : Pattern) (ha : d816 p = 1) (hb : d125748 p = 1) : d11152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d125748 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d125748 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d125748 q = 1) : d11152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22642 (p : Pattern) (ha : d8602 p = 1) (hb : d125748 p = 1) : d126077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d125748 q = 1) : d126076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8602 q = 1) (hb : d125748 q = 1) : d126077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, d126077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, d126077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22643 (p : Pattern) (ha : d8609 p = 1) (hb : d125748 p = 1) : d126084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d125748 q = 1) : d126082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d125748 q = 1) : d126083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8609 q = 1) (hb : d125748 q = 1) : d126084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, d126084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, d126084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22644 (p : Pattern) (ha : d8615 p = 1) (hb : d125748 p = 1) : d126091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d839 q = 1) : d839 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d840 q = 1) (hb : d85721 q = 1) : d11156 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d841 q = 1) (hb : d85721 q = 1) : d11157 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d842 q = 1) (hb : d85721 q = 1) : d11158 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8613 q = 1) (hb : d125746 q = 1) : d126088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d125746, d126088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8613, d125746, d126088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d759 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d759, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d760 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d760, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d761 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d761, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6875 q = 1) (hb : d125747 q = 1) : d126089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d125747, d126089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6875, d125747, d126089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8614 q = 1) (hb : d125748 q = 1) : d126090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8614, d125748, d126090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8614, d125748, d126090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8615 q = 1) (hb : d125748 q = 1) : d126091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8615, d126091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8615, d126091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22645 (p : Pattern) (ha : d8621 p = 1) (hb : d125748 p = 1) : d126097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d125748 q = 1) : d126092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22644 q ha hb
    | true =>
      simp only [d8616, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d125748 q = 1) : d126093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22637 q ha hb
    | true =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d125748 q = 1) : d126094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d125748 q = 1) : d126095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d125748 q = 1) : d126096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8621 q = 1) (hb : d125748 q = 1) : d126097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, d126097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, d126097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22646 (p : Pattern) (ha : d8641 p = 1) (hb : d125748 p = 1) : d126103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d125748 q = 1) : d126100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d125748 q = 1) : d126101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d125748 q = 1) : d126102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8641 q = 1) (hb : d125748 q = 1) : d126103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d126103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d126103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22647 (p : Pattern) (ha : d94308 p = 1) (hb : d125748 p = 1) : d126109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d125748 q = 1) : d126078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22642 q ha hb
    | true =>
      simp only [d8603, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22640 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d125748 q = 1) : d126079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d125748 q = 1) : d126080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d125748 q = 1) : d126081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d125748 q = 1) : d126085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22643 q ha hb
    | true =>
      simp only [d8610, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22641 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d125748 q = 1) : d126086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d125748 q = 1) : d126087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d125748 q = 1) : d126098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22645 q ha hb
    | true =>
      simp only [d8626, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22638 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d125748 q = 1) : d126099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d125748 q = 1) : d126104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22646 q ha hb
    | true =>
      simp only [d8642, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d125748 q = 1) : d126105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d125748 q = 1) : d126106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d125748 q = 1) : d126107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d125748 q = 1) : d126108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94308 q = 1) (hb : d125748 q = 1) : d126109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d126109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d126109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22648 (p : Pattern) (ha : d916 p = 1) (hb : d125748 p = 1) : d11214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d125748 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d125748 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d125748 q = 1) : d11214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22649 (p : Pattern) (ha : d922 p = 1) (hb : d125748 p = 1) : d11220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d125748 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d125748 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d125748 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d125748 q = 1) : d11220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22650 (p : Pattern) (ha : d8648 p = 1) (hb : d125748 p = 1) : d126110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d125748 q = 1) : d126076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8648 q = 1) (hb : d125748 q = 1) : d126110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, d126110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8648, d126110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22651 (p : Pattern) (ha : d8653 p = 1) (hb : d125748 p = 1) : d126115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d125748 q = 1) : d126082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d125748 q = 1) : d126083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8653 q = 1) (hb : d125748 q = 1) : d126115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, d126115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8653, d126115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22652 (p : Pattern) (ha : d8657 p = 1) (hb : d125748 p = 1) : d126119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d125748 q = 1) : d126092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22644 q ha hb
    | true =>
      simp only [d8616, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d125748 q = 1) : d126093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22637 q ha hb
    | true =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d125748 q = 1) : d126094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d125748 q = 1) : d126095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d125748 q = 1) : d126096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8657 q = 1) (hb : d125748 q = 1) : d126119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, d126119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8657, d126119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22653 (p : Pattern) (ha : d8658 p = 1) (hb : d125748 p = 1) : d126066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22637 q ha hb
    | true =>
      simp only [d6878, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d125748 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22624 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8658 q = 1) (hb : d125748 q = 1) : d126066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8658, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22654 (p : Pattern) (ha : d8663 p = 1) (hb : d125748 p = 1) : d126122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22632 q ha hb
    | true =>
      simp only [d8577, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d125748 q = 1) : d126100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d125748 q = 1) : d126101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d125748 q = 1) : d126102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d125748 q = 1) : d126122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d126122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d126122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22655 (p : Pattern) (ha : d94313 p = 1) (hb : d125748 p = 1) : d126128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d125748 q = 1) : d126078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22642 q ha hb
    | true =>
      simp only [d8603, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22640 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d125748 q = 1) : d126079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d125748 q = 1) : d126080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d125748 q = 1) : d126081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d125748 q = 1) : d126085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22643 q ha hb
    | true =>
      simp only [d8610, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22641 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d125748 q = 1) : d126086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d125748 q = 1) : d126087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d125748 q = 1) : d126098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22645 q ha hb
    | true =>
      simp only [d8626, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22638 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d125748 q = 1) : d126099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d125748 q = 1) : d126104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22646 q ha hb
    | true =>
      simp only [d8642, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d125748 q = 1) : d126105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d125748 q = 1) : d126106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d125748 q = 1) : d126107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d125748 q = 1) : d126108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8649 q = 1) (hb : d125748 q = 1) : d126111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d126111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22650 q ha hb
    | true =>
      simp only [d8649, d126111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22648 q ha hb
  have h16 (q : Pattern) (ha : d8650 q = 1) (hb : d125748 q = 1) : d126112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d126112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d126112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8651 q = 1) (hb : d125748 q = 1) : d126113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d126113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8651, d126113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8652 q = 1) (hb : d125748 q = 1) : d126114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d126114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d126114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8654 q = 1) (hb : d125748 q = 1) : d126116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d126116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22651 q ha hb
    | true =>
      simp only [d8654, d126116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22649 q ha hb
  have h20 (q : Pattern) (ha : d8655 q = 1) (hb : d125748 q = 1) : d126117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d126117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d126117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8656 q = 1) (hb : d125748 q = 1) : d126118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d126118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8656, d126118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8659 q = 1) (hb : d125748 q = 1) : d126120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22652 q ha hb
    | true =>
      simp only [d8659, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22653 q ha hb
  have h23 (q : Pattern) (ha : d94309 q = 1) (hb : d125748 q = 1) : d126121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94309, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8664 q = 1) (hb : d125748 q = 1) : d126123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22654 q ha hb
    | true =>
      simp only [d8664, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8665 q = 1) (hb : d125748 q = 1) : d126124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8665, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94310 q = 1) (hb : d125748 q = 1) : d126125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94310, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94311 q = 1) (hb : d125748 q = 1) : d126126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d126126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94311, d126126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94312 q = 1) (hb : d125748 q = 1) : d126127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d126127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94312, d126127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94313 q = 1) (hb : d125748 q = 1) : d126128 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d126128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94313, d126128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22656 (p : Pattern) (ha : d94320 p = 1) (hb : d125748 p = 1) : d126137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d125748 q = 1) : d126120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22652 q ha hb
    | true =>
      simp only [d8659, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22653 q ha hb
  have h2 (q : Pattern) (ha : d94309 q = 1) (hb : d125748 q = 1) : d126121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94309, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8664 q = 1) (hb : d125748 q = 1) : d126123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22654 q ha hb
    | true =>
      simp only [d8664, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8665 q = 1) (hb : d125748 q = 1) : d126124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8665, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d125748 q = 1) : d126125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d125748 q = 1) : d126135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d126135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d126135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d125748 q = 1) : d126136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d126136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d126136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d125748 q = 1) : d126137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d126137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d126137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22657 (p : Pattern) (ha : d6923 p = 1) (hb : d125748 p = 1) : d126151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6921 q = 1) (hb : d125746 q = 1) : d126149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6921, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6210 q = 1) (hb : d94753 q = 1) : d6210 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6211 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6211, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d6212 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6212, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6213 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6213, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6214 q = 1) (hb : d125747 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6214, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d6922 q = 1) (hb : d125748 q = 1) : d126150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6922, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6923 q = 1) (hb : d125748 q = 1) : d126151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d6923, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22658 (p : Pattern) (ha : d8691 p = 1) (hb : d125748 p = 1) : d126146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d970 q = 1) : d970 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d977 q = 1) (hb : d85721 q = 1) : d11264 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d978 q = 1) (hb : d85721 q = 1) : d11265 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d979 q = 1) (hb : d85721 q = 1) : d11266 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8689 q = 1) (hb : d125746 q = 1) : d126143 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d125746, d126143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8689, d125746, d126143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d982 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d982, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d983 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d983, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d984 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d984, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6921 q = 1) (hb : d125747 q = 1) : d126144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d125747, d126144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6921, d125747, d126144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8690 q = 1) (hb : d125748 q = 1) : d126145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d125748, d126145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8690, d125748, d126145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8691 q = 1) (hb : d125748 q = 1) : d126146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d126146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8691, d126146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22659 (p : Pattern) (ha : d8697 p = 1) (hb : d125748 p = 1) : d126157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d125748 q = 1) : d126147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d126147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22658 q ha hb
    | true =>
      simp only [d8692, d126147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d125748 q = 1) : d126148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d126148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d126148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22657 q ha hb
    | true =>
      simp only [d6924, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d125748 q = 1) : d126154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d126154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, d126154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8695 q = 1) (hb : d125748 q = 1) : d126155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d126155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, d126155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8696 q = 1) (hb : d125748 q = 1) : d126156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d126156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8696, d126156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8697 q = 1) (hb : d125748 q = 1) : d126157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d126157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8697, d126157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22660 (p : Pattern) (ha : d8701 p = 1) (hb : d125748 p = 1) : d126161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22657 q ha hb
    | true =>
      simp only [d6924, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d125748 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22629 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d125748 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8698 q = 1) (hb : d125748 q = 1) : d126158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8699 q = 1) (hb : d125748 q = 1) : d126159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8699, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8700 q = 1) (hb : d125748 q = 1) : d126160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8700, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8701 q = 1) (hb : d125748 q = 1) : d126161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8701, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22661 (p : Pattern) (ha : d8715 p = 1) (hb : d125748 p = 1) : d126151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6921 q = 1) (hb : d125746 q = 1) : d126149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6921, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d987 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d987, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d988 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d988, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d989 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d989, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d995 q = 1) (hb : d125747 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d995, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8714 q = 1) (hb : d125748 q = 1) : d126150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8714, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8715 q = 1) (hb : d125748 q = 1) : d126151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8715, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22662 (p : Pattern) (ha : d8721 p = 1) (hb : d125748 p = 1) : d126167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22661 q ha hb
    | true =>
      simp only [d8716, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d125748 q = 1) : d126164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d126164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d126164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d125748 q = 1) : d126165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d126165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d126165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d125748 q = 1) : d126166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d126166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d126166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d125748 q = 1) : d126167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d126167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d126167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22663 (p : Pattern) (ha : d94330 p = 1) (hb : d125748 p = 1) : d126173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d125748 q = 1) : d126162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d126162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22659 q ha hb
    | true =>
      simp only [d8702, d126162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22660 q ha hb
  have h2 (q : Pattern) (ha : d94326 q = 1) (hb : d125748 q = 1) : d126163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d126163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94326, d126163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8722 q = 1) (hb : d125748 q = 1) : d126168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d126168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22662 q ha hb
    | true =>
      simp only [d8722, d126168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8723 q = 1) (hb : d125748 q = 1) : d126169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d126169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8723, d126169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d125748 q = 1) : d126170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d126170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, d126170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d125748 q = 1) : d126171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d126171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d126171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d125748 q = 1) : d126172 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d126172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d126172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d125748 q = 1) : d126173 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d126173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d126173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22664 (p : Pattern) (ha : d94336 p = 1) (hb : d125748 p = 1) : d126179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d125748 q = 1) : d126064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d126064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d126064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22634 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d125748 q = 1) : d126065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d126065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d126065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d125748 q = 1) : d126073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22634 q ha hb
    | true =>
      simp only [d8598, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22636 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d125748 q = 1) : d126074 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d125748 q = 1) : d126075 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d126075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d126075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94314 q = 1) (hb : d125748 q = 1) : d126129 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d126129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22647 q ha hb
    | true =>
      simp only [d94314, d126129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22655 q ha hb
  have h7 (q : Pattern) (ha : d8677 q = 1) (hb : d125748 q = 1) : d126131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d126131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22639 q ha hb
    | true =>
      simp only [d8677, d126131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22627 q ha hb
  have h8 (q : Pattern) (ha : d94315 q = 1) (hb : d125748 q = 1) : d126132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d126132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, d126132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94316 q = 1) (hb : d125748 q = 1) : d126133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d126133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94316, d126133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94317 q = 1) (hb : d125748 q = 1) : d126134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d126134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94317, d126134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94321 q = 1) (hb : d125748 q = 1) : d126138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d126138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94321, d126138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22656 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d125748 q = 1) : d11259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22628 q ha hb
  have h13 (q : Pattern) (ha : d94322 q = 1) (hb : d125748 q = 1) : d126139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d126139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94322, d126139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94323 q = 1) (hb : d125748 q = 1) : d126140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d126140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94323, d126140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94324 q = 1) (hb : d125748 q = 1) : d126141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d126141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94324, d126141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94325 q = 1) (hb : d125748 q = 1) : d126142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d126142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94325, d126142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94331 q = 1) (hb : d125748 q = 1) : d126174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d126174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94331, d126174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22663 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d125748 q = 1) : d11352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22631 q ha hb
  have h19 (q : Pattern) (ha : d94332 q = 1) (hb : d125748 q = 1) : d126175 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d126175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94332, d126175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94333 q = 1) (hb : d125748 q = 1) : d126176 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d126176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94333, d126176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94334 q = 1) (hb : d125748 q = 1) : d126177 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d126177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94334, d126177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94335 q = 1) (hb : d125748 q = 1) : d126178 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d126178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94335, d126178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94336 q = 1) (hb : d125748 q = 1) : d126179 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d126179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94336, d126179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22665 (p : Pattern) (ha : d94342 p = 1) (hb : d125748 p = 1) : d126185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d125748 q = 1) : d126180 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d126180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d126180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22664 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d125748 q = 1) : d126181 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d126181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d126181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d125748 q = 1) : d126182 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d126182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d126182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d125748 q = 1) : d126183 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d126183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d126183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d125748 q = 1) : d126184 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d126184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d126184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d125748 q = 1) : d126185 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d126185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d126185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22666 (p : Pattern) (ha : d1152 p = 1) (hb : d125748 p = 1) : d11379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1146 q = 1) (hb : d125746 q = 1) : d11373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d125746, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1146, d125746, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1151 q = 1) (hb : d125748 q = 1) : d11378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d125748, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1151, d125748, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1152 q = 1) (hb : d125748 q = 1) : d11379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22667 (p : Pattern) (ha : d1162 p = 1) (hb : d125748 p = 1) : d11389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d125748 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d125748 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d125748 q = 1) : d11389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22668 (p : Pattern) (ha : d1172 p = 1) (hb : d125748 p = 1) : d11399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d125748 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d125748 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d125748 q = 1) : d11399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22669 (p : Pattern) (ha : d1361 p = 1) (hb : d125748 p = 1) : d11519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d125748 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22667 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d125748 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d125748 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d125748 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d125748 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d125748 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22668 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d125748 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d125748 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d125748 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d125748 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d125748 q = 1) : d11519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22670 (p : Pattern) (ha : d1370 p = 1) (hb : d125748 p = 1) : d11528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d125748 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22668 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d125748 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d125748 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d125748 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d125748 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d125748 q = 1) : d11528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22671 (p : Pattern) (ha : d1430 p = 1) (hb : d125748 p = 1) : d11559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1420 q = 1) (hb : d125746 q = 1) : d11549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d125746, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1420, d125746, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1429 q = 1) (hb : d125748 q = 1) : d11558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d125748, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1429, d125748, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1430 q = 1) (hb : d125748 q = 1) : d11559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22672 (p : Pattern) (ha : d1497 p = 1) (hb : d125748 p = 1) : d11615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d125748 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22671 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d125748 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d125748 q = 1) : d11612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d125748 q = 1) : d11613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d125748 q = 1) : d11614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d125748 q = 1) : d11615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22673 (p : Pattern) (ha : d1503 p = 1) (hb : d125748 p = 1) : d11621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d125748 q = 1) : d11616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22672 q ha hb
    | true =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d125748 q = 1) : d11617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d125748 q = 1) : d11618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d125748 q = 1) : d11619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d125748 q = 1) : d11620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d125748 q = 1) : d11621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22674 (p : Pattern) (ha : d8743 p = 1) (hb : d125748 p = 1) : d126190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6954 q = 1) (hb : d125746 q = 1) : d126188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6954, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1142 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d1142, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1143 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1143, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1144 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1144, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1146 q = 1) (hb : d125747 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1146, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8742 q = 1) (hb : d125748 q = 1) : d126189 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8742, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8743 q = 1) (hb : d125748 q = 1) : d126190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8743, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22675 (p : Pattern) (ha : d8749 p = 1) (hb : d125748 p = 1) : d126196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8749 q = 1) (hb : d125748 q = 1) : d126196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22676 (p : Pattern) (ha : d8755 p = 1) (hb : d125748 p = 1) : d126202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22675 q ha hb
    | true =>
      simp only [d8750, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22667 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8755 q = 1) (hb : d125748 q = 1) : d126202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22677 (p : Pattern) (ha : d8758 p = 1) (hb : d125748 p = 1) : d126205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8758 q = 1) (hb : d125748 q = 1) : d126205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8758, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22678 (p : Pattern) (ha : d8764 p = 1) (hb : d125748 p = 1) : d126211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22675 q ha hb
    | true =>
      simp only [d8750, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22667 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8759 q = 1) (hb : d125748 q = 1) : d126206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22677 q ha hb
    | true =>
      simp only [d8759, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22668 q ha hb
  have h7 (q : Pattern) (ha : d8760 q = 1) (hb : d125748 q = 1) : d126207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8761 q = 1) (hb : d125748 q = 1) : d126208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8761, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8762 q = 1) (hb : d125748 q = 1) : d126209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8763 q = 1) (hb : d125748 q = 1) : d126210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8764 q = 1) (hb : d125748 q = 1) : d126211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8764, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22679 (p : Pattern) (ha : d6956 p = 1) (hb : d125748 p = 1) : d126190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6954 q = 1) (hb : d125746 q = 1) : d126188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6954, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5009 q = 1) (hb : d94753 q = 1) : d5009 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5023 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5024 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5024, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d5025 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5025, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5026 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5026, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5027 q = 1) (hb : d125747 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5027, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d6955 q = 1) (hb : d125748 q = 1) : d126189 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6955, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d6956 q = 1) (hb : d125748 q = 1) : d126190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d6956, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22680 (p : Pattern) (ha : d8792 p = 1) (hb : d125748 p = 1) : d126196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22679 q ha hb
    | true =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8792 q = 1) (hb : d125748 q = 1) : d126196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22681 (p : Pattern) (ha : d8843 p = 1) (hb : d125748 p = 1) : d126269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8838 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22680 q ha hb
    | true =>
      simp only [d8838, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22667 q ha hb
  have h2 (q : Pattern) (ha : d8839 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8840 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8840, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8841 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8842 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d125748 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22667 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d125748 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d125748 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d125748 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d125748 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8843 q = 1) (hb : d125748 q = 1) : d126269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d126269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8843, d126269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22682 (p : Pattern) (ha : d1185 p = 1) (hb : d125748 p = 1) : d11412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d125748 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d125748 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d125748 q = 1) : d11412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22683 (p : Pattern) (ha : d1195 p = 1) (hb : d125748 p = 1) : d11422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d125748 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d125748 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d125748 q = 1) : d11422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22684 (p : Pattern) (ha : d8769 p = 1) (hb : d125748 p = 1) : d126216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d125748 q = 1) : d126215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8769 q = 1) (hb : d125748 q = 1) : d126216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d126216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d126216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22685 (p : Pattern) (ha : d8776 p = 1) (hb : d125748 p = 1) : d126223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d125748 q = 1) : d126221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d125748 q = 1) : d126222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8776 q = 1) (hb : d125748 q = 1) : d126223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d126223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d126223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22686 (p : Pattern) (ha : d8782 p = 1) (hb : d125748 p = 1) : d126230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1215 q = 1) : d1215 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1216 q = 1) (hb : d85721 q = 1) : d11426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1217 q = 1) (hb : d85721 q = 1) : d11427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1218 q = 1) (hb : d85721 q = 1) : d11428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8780 q = 1) (hb : d125746 q = 1) : d126227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d125746, d126227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8780, d125746, d126227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1129 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d1129, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1130 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1130, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1131 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1131, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6954 q = 1) (hb : d125747 q = 1) : d126228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d125747, d126228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6954, d125747, d126228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8781 q = 1) (hb : d125748 q = 1) : d126229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d125748, d126229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8781, d125748, d126229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8782 q = 1) (hb : d125748 q = 1) : d126230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d126230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8782, d126230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22687 (p : Pattern) (ha : d8788 p = 1) (hb : d125748 p = 1) : d126236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d125748 q = 1) : d126231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22686 q ha hb
    | true =>
      simp only [d8783, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d125748 q = 1) : d126232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22679 q ha hb
    | true =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d125748 q = 1) : d126233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d125748 q = 1) : d126234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d125748 q = 1) : d126235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8788 q = 1) (hb : d125748 q = 1) : d126236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d126236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d126236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22688 (p : Pattern) (ha : d8808 p = 1) (hb : d125748 p = 1) : d126242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d125748 q = 1) : d126239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d125748 q = 1) : d126240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d125748 q = 1) : d126241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d125748 q = 1) : d126242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d126242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d126242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22689 (p : Pattern) (ha : d94349 p = 1) (hb : d125748 p = 1) : d126248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d125748 q = 1) : d126217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22684 q ha hb
    | true =>
      simp only [d8770, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22682 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d125748 q = 1) : d126218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d125748 q = 1) : d126219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d125748 q = 1) : d126220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d125748 q = 1) : d126224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22685 q ha hb
    | true =>
      simp only [d8777, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22683 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d125748 q = 1) : d126225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d125748 q = 1) : d126226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d125748 q = 1) : d126237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22687 q ha hb
    | true =>
      simp only [d8793, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22680 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d125748 q = 1) : d126238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d125748 q = 1) : d126243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22688 q ha hb
    | true =>
      simp only [d8809, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d125748 q = 1) : d126244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d125748 q = 1) : d126245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d125748 q = 1) : d126246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d125748 q = 1) : d126247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94349 q = 1) (hb : d125748 q = 1) : d126248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d126248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d126248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22690 (p : Pattern) (ha : d1327 p = 1) (hb : d125748 p = 1) : d11484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d125748 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d125748 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d125748 q = 1) : d11484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22691 (p : Pattern) (ha : d1333 p = 1) (hb : d125748 p = 1) : d11490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d125748 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d125748 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d125748 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d125748 q = 1) : d11490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22692 (p : Pattern) (ha : d8815 p = 1) (hb : d125748 p = 1) : d126249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d125748 q = 1) : d126215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8815 q = 1) (hb : d125748 q = 1) : d126249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d126249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8815, d126249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22693 (p : Pattern) (ha : d8820 p = 1) (hb : d125748 p = 1) : d126254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d125748 q = 1) : d126221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d125748 q = 1) : d126222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8820 q = 1) (hb : d125748 q = 1) : d126254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d126254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8820, d126254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22694 (p : Pattern) (ha : d8824 p = 1) (hb : d125748 p = 1) : d126258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d125748 q = 1) : d126231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22686 q ha hb
    | true =>
      simp only [d8783, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d125748 q = 1) : d126232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22679 q ha hb
    | true =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d125748 q = 1) : d126233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d125748 q = 1) : d126234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d125748 q = 1) : d126235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8824 q = 1) (hb : d125748 q = 1) : d126258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d126258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8824, d126258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22695 (p : Pattern) (ha : d8825 p = 1) (hb : d125748 p = 1) : d126205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22679 q ha hb
    | true =>
      simp only [d6957, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d125748 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22666 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8825 q = 1) (hb : d125748 q = 1) : d126205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8825, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22696 (p : Pattern) (ha : d8830 p = 1) (hb : d125748 p = 1) : d126261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22674 q ha hb
    | true =>
      simp only [d8744, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d125748 q = 1) : d126239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d125748 q = 1) : d126240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d125748 q = 1) : d126241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d125748 q = 1) : d126261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d126261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d126261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22697 (p : Pattern) (ha : d94354 p = 1) (hb : d125748 p = 1) : d126267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d125748 q = 1) : d126217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22684 q ha hb
    | true =>
      simp only [d8770, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22682 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d125748 q = 1) : d126218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d125748 q = 1) : d126219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d125748 q = 1) : d126220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d125748 q = 1) : d126224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22685 q ha hb
    | true =>
      simp only [d8777, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22683 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d125748 q = 1) : d126225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d125748 q = 1) : d126226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d125748 q = 1) : d126237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22687 q ha hb
    | true =>
      simp only [d8793, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22680 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d125748 q = 1) : d126238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d125748 q = 1) : d126243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22688 q ha hb
    | true =>
      simp only [d8809, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d125748 q = 1) : d126244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d125748 q = 1) : d126245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d125748 q = 1) : d126246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d125748 q = 1) : d126247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8816 q = 1) (hb : d125748 q = 1) : d126250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d126250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22692 q ha hb
    | true =>
      simp only [d8816, d126250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22690 q ha hb
  have h16 (q : Pattern) (ha : d8817 q = 1) (hb : d125748 q = 1) : d126251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d126251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d126251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8818 q = 1) (hb : d125748 q = 1) : d126252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d126252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8818, d126252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8819 q = 1) (hb : d125748 q = 1) : d126253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d126253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d126253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8821 q = 1) (hb : d125748 q = 1) : d126255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d126255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22693 q ha hb
    | true =>
      simp only [d8821, d126255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22691 q ha hb
  have h20 (q : Pattern) (ha : d8822 q = 1) (hb : d125748 q = 1) : d126256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d126256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d126256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8823 q = 1) (hb : d125748 q = 1) : d126257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d126257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8823, d126257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8826 q = 1) (hb : d125748 q = 1) : d126259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22694 q ha hb
    | true =>
      simp only [d8826, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22695 q ha hb
  have h23 (q : Pattern) (ha : d94350 q = 1) (hb : d125748 q = 1) : d126260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94350, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8831 q = 1) (hb : d125748 q = 1) : d126262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22696 q ha hb
    | true =>
      simp only [d8831, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8832 q = 1) (hb : d125748 q = 1) : d126263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8832, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94351 q = 1) (hb : d125748 q = 1) : d126264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94351, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94352 q = 1) (hb : d125748 q = 1) : d126265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d126265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94352, d126265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94353 q = 1) (hb : d125748 q = 1) : d126266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d126266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94353, d126266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94354 q = 1) (hb : d125748 q = 1) : d126267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d126267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94354, d126267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22698 (p : Pattern) (ha : d94361 p = 1) (hb : d125748 p = 1) : d126276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d125748 q = 1) : d126259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22694 q ha hb
    | true =>
      simp only [d8826, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22695 q ha hb
  have h2 (q : Pattern) (ha : d94350 q = 1) (hb : d125748 q = 1) : d126260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94350, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8831 q = 1) (hb : d125748 q = 1) : d126262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22696 q ha hb
    | true =>
      simp only [d8831, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8832 q = 1) (hb : d125748 q = 1) : d126263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8832, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d125748 q = 1) : d126264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d125748 q = 1) : d126274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d126274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d126274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d125748 q = 1) : d126275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d126275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d126275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d125748 q = 1) : d126276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d126276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d126276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22699 (p : Pattern) (ha : d7002 p = 1) (hb : d125748 p = 1) : d126290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7000 q = 1) (hb : d125746 q = 1) : d126288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7000, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6349 q = 1) (hb : d94753 q = 1) : d6349 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6355 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6356 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6356, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d6357 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6357, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6358 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6358, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6359 q = 1) (hb : d125747 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6359, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d7001 q = 1) (hb : d125748 q = 1) : d126289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7001, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7002 q = 1) (hb : d125748 q = 1) : d126290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d7002, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22700 (p : Pattern) (ha : d8858 p = 1) (hb : d125748 p = 1) : d126285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1390 q = 1) : d1390 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1397 q = 1) (hb : d85721 q = 1) : d11534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1398 q = 1) (hb : d85721 q = 1) : d11535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1399 q = 1) (hb : d85721 q = 1) : d11536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8856 q = 1) (hb : d125746 q = 1) : d126282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d125746, d126282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8856, d125746, d126282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1402 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d1402, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1403 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1403, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1404 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1404, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7000 q = 1) (hb : d125747 q = 1) : d126283 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d125747, d126283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7000, d125747, d126283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8857 q = 1) (hb : d125748 q = 1) : d126284 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d125748, d126284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8857, d125748, d126284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8858 q = 1) (hb : d125748 q = 1) : d126285 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d126285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8858, d126285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22701 (p : Pattern) (ha : d8864 p = 1) (hb : d125748 p = 1) : d126296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d125748 q = 1) : d126286 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d126286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22700 q ha hb
    | true =>
      simp only [d8859, d126286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d125748 q = 1) : d126287 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d126287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d126287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22699 q ha hb
    | true =>
      simp only [d7003, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d125748 q = 1) : d126293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d126293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, d126293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8862 q = 1) (hb : d125748 q = 1) : d126294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d126294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, d126294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8863 q = 1) (hb : d125748 q = 1) : d126295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d126295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8863, d126295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8864 q = 1) (hb : d125748 q = 1) : d126296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d126296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8864, d126296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22702 (p : Pattern) (ha : d8868 p = 1) (hb : d125748 p = 1) : d126300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22699 q ha hb
    | true =>
      simp only [d7003, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d125748 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22671 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d125748 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8865 q = 1) (hb : d125748 q = 1) : d126297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8866 q = 1) (hb : d125748 q = 1) : d126298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8866, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8867 q = 1) (hb : d125748 q = 1) : d126299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8867, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8868 q = 1) (hb : d125748 q = 1) : d126300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8868, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22703 (p : Pattern) (ha : d8882 p = 1) (hb : d125748 p = 1) : d126290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7000 q = 1) (hb : d125746 q = 1) : d126288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7000, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1412 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d1412, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1413 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1413, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1414 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1414, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1420 q = 1) (hb : d125747 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1420, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8881 q = 1) (hb : d125748 q = 1) : d126289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8881, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8882 q = 1) (hb : d125748 q = 1) : d126290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8882, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22704 (p : Pattern) (ha : d8888 p = 1) (hb : d125748 p = 1) : d126306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22703 q ha hb
    | true =>
      simp only [d8883, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d125748 q = 1) : d126303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d126303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d126303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d125748 q = 1) : d126304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d126304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d126304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d125748 q = 1) : d126305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d126305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d126305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d125748 q = 1) : d126306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d126306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d126306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22705 (p : Pattern) (ha : d94371 p = 1) (hb : d125748 p = 1) : d126312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d125748 q = 1) : d126301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d126301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22701 q ha hb
    | true =>
      simp only [d8869, d126301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22702 q ha hb
  have h2 (q : Pattern) (ha : d94367 q = 1) (hb : d125748 q = 1) : d126302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d126302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94367, d126302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8889 q = 1) (hb : d125748 q = 1) : d126307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d126307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22704 q ha hb
    | true =>
      simp only [d8889, d126307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8890 q = 1) (hb : d125748 q = 1) : d126308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d126308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8890, d126308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d125748 q = 1) : d126309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d126309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, d126309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d125748 q = 1) : d126310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d126310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d126310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d125748 q = 1) : d126311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d126311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d126311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d125748 q = 1) : d126312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d126312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d126312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22706 (p : Pattern) (ha : d94377 p = 1) (hb : d125748 p = 1) : d126318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d125748 q = 1) : d126203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d126203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d126203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22676 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d125748 q = 1) : d126204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d126204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d126204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d125748 q = 1) : d126212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22676 q ha hb
    | true =>
      simp only [d8765, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22678 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d125748 q = 1) : d126213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d125748 q = 1) : d126214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d126214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d126214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94355 q = 1) (hb : d125748 q = 1) : d126268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d126268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22689 q ha hb
    | true =>
      simp only [d94355, d126268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22697 q ha hb
  have h7 (q : Pattern) (ha : d8844 q = 1) (hb : d125748 q = 1) : d126270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d126270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22681 q ha hb
    | true =>
      simp only [d8844, d126270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22669 q ha hb
  have h8 (q : Pattern) (ha : d94356 q = 1) (hb : d125748 q = 1) : d126271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d126271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, d126271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94357 q = 1) (hb : d125748 q = 1) : d126272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d126272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94357, d126272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94358 q = 1) (hb : d125748 q = 1) : d126273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d126273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94358, d126273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94362 q = 1) (hb : d125748 q = 1) : d126277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d126277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94362, d126277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22698 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d125748 q = 1) : d11529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22670 q ha hb
  have h13 (q : Pattern) (ha : d94363 q = 1) (hb : d125748 q = 1) : d126278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d126278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94363, d126278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94364 q = 1) (hb : d125748 q = 1) : d126279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d126279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94364, d126279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94365 q = 1) (hb : d125748 q = 1) : d126280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d126280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94365, d126280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94366 q = 1) (hb : d125748 q = 1) : d126281 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d126281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94366, d126281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94372 q = 1) (hb : d125748 q = 1) : d126313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d126313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94372, d126313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22705 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d125748 q = 1) : d11622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22673 q ha hb
  have h19 (q : Pattern) (ha : d94373 q = 1) (hb : d125748 q = 1) : d126314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d126314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94373, d126314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94374 q = 1) (hb : d125748 q = 1) : d126315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d126315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94374, d126315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94375 q = 1) (hb : d125748 q = 1) : d126316 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d126316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94375, d126316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94376 q = 1) (hb : d125748 q = 1) : d126317 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d126317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94376, d126317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94377 q = 1) (hb : d125748 q = 1) : d126318 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d126318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94377, d126318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22707 (p : Pattern) (ha : d94383 p = 1) (hb : d125748 p = 1) : d126324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d125748 q = 1) : d126319 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d126319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d126319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22706 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d125748 q = 1) : d126320 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d126320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d126320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d125748 q = 1) : d126321 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d126321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d126321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d125748 q = 1) : d126322 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d126322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d126322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d125748 q = 1) : d126323 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d126323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d126323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d125748 q = 1) : d126324 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d126324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d126324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22708 (p : Pattern) (ha : d1613 p = 1) (hb : d125748 p = 1) : d11650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1607 q = 1) (hb : d125746 q = 1) : d11644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d125746, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1607, d125746, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1612 q = 1) (hb : d125748 q = 1) : d11649 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d125748, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1612, d125748, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1613 q = 1) (hb : d125748 q = 1) : d11650 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22709 (p : Pattern) (ha : d1623 p = 1) (hb : d125748 p = 1) : d11660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d125748 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d125748 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d125748 q = 1) : d11660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22710 (p : Pattern) (ha : d1633 p = 1) (hb : d125748 p = 1) : d11670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d125748 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d125748 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d125748 q = 1) : d11670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22711 (p : Pattern) (ha : d1838 p = 1) (hb : d125748 p = 1) : d11790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d125748 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22709 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d125748 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d125748 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d125748 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d125748 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d125748 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22710 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d125748 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d125748 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d125748 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d125748 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d125748 q = 1) : d11790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22712 (p : Pattern) (ha : d1847 p = 1) (hb : d125748 p = 1) : d11799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d125748 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22710 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d125748 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d125748 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d125748 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d125748 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d125748 q = 1) : d11799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22713 (p : Pattern) (ha : d1907 p = 1) (hb : d125748 p = 1) : d11830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1897 q = 1) (hb : d125746 q = 1) : d11820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d125746, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1897, d125746, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d125747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1906 q = 1) (hb : d125748 q = 1) : d11829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d125748, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1906, d125748, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1907 q = 1) (hb : d125748 q = 1) : d11830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22714 (p : Pattern) (ha : d1974 p = 1) (hb : d125748 p = 1) : d11886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d125748 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22713 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d125748 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d125748 q = 1) : d11883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d125748 q = 1) : d11884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d125748 q = 1) : d11885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d125748 q = 1) : d11886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22715 (p : Pattern) (ha : d1980 p = 1) (hb : d125748 p = 1) : d11892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d125748 q = 1) : d11887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22714 q ha hb
    | true =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d125748 q = 1) : d11888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d125748 q = 1) : d11889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d125748 q = 1) : d11890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d125748 q = 1) : d11891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d125748 q = 1) : d11892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22716 (p : Pattern) (ha : d8911 p = 1) (hb : d125748 p = 1) : d126330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7034 q = 1) (hb : d125746 q = 1) : d126328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7034, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1603 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d1603, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1604 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1604, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1605 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1605, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1607 q = 1) (hb : d125747 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1607, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8910 q = 1) (hb : d125748 q = 1) : d126329 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8910, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8911 q = 1) (hb : d125748 q = 1) : d126330 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8911, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22717 (p : Pattern) (ha : d8917 p = 1) (hb : d125748 p = 1) : d126336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8917 q = 1) (hb : d125748 q = 1) : d126336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22718 (p : Pattern) (ha : d8923 p = 1) (hb : d125748 p = 1) : d126342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22717 q ha hb
    | true =>
      simp only [d8918, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22709 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8923 q = 1) (hb : d125748 q = 1) : d126342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22719 (p : Pattern) (ha : d8926 p = 1) (hb : d125748 p = 1) : d126345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8926 q = 1) (hb : d125748 q = 1) : d126345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8926, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22720 (p : Pattern) (ha : d8932 p = 1) (hb : d125748 p = 1) : d126351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22717 q ha hb
    | true =>
      simp only [d8918, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22709 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8927 q = 1) (hb : d125748 q = 1) : d126346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22719 q ha hb
    | true =>
      simp only [d8927, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22710 q ha hb
  have h7 (q : Pattern) (ha : d8928 q = 1) (hb : d125748 q = 1) : d126347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8929 q = 1) (hb : d125748 q = 1) : d126348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8929, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8930 q = 1) (hb : d125748 q = 1) : d126349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8931 q = 1) (hb : d125748 q = 1) : d126350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8932 q = 1) (hb : d125748 q = 1) : d126351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8932, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22721 (p : Pattern) (ha : d7036 p = 1) (hb : d125748 p = 1) : d126330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7034 q = 1) (hb : d125746 q = 1) : d126328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7034, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5120 q = 1) (hb : d94753 q = 1) : d5120 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5139 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5140 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5140, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d5141 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5141, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5142 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5142, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5143 q = 1) (hb : d125747 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5143, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d7035 q = 1) (hb : d125748 q = 1) : d126329 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7035, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7036 q = 1) (hb : d125748 q = 1) : d126330 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d7036, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22722 (p : Pattern) (ha : d8960 p = 1) (hb : d125748 p = 1) : d126336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22721 q ha hb
    | true =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8960 q = 1) (hb : d125748 q = 1) : d126336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22723 (p : Pattern) (ha : d9011 p = 1) (hb : d125748 p = 1) : d126409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9006 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22722 q ha hb
    | true =>
      simp only [d9006, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22709 q ha hb
  have h2 (q : Pattern) (ha : d9007 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9008 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9008, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9009 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9010 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d125748 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22709 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d125748 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d125748 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d125748 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d125748 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9011 q = 1) (hb : d125748 q = 1) : d126409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d126409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9011, d126409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22724 (p : Pattern) (ha : d1646 p = 1) (hb : d125748 p = 1) : d11683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d125748 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d125748 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d125748 q = 1) : d11683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22725 (p : Pattern) (ha : d1656 p = 1) (hb : d125748 p = 1) : d11693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d125748 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d125748 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d125748 q = 1) : d11693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22726 (p : Pattern) (ha : d8937 p = 1) (hb : d125748 p = 1) : d126356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d125748 q = 1) : d126355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8937 q = 1) (hb : d125748 q = 1) : d126356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d126356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d126356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22727 (p : Pattern) (ha : d8944 p = 1) (hb : d125748 p = 1) : d126363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d125748 q = 1) : d126361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d125748 q = 1) : d126362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8944 q = 1) (hb : d125748 q = 1) : d126363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d126363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d126363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22728 (p : Pattern) (ha : d8950 p = 1) (hb : d125748 p = 1) : d126370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1670 q = 1) : d1670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1671 q = 1) (hb : d85721 q = 1) : d11697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1672 q = 1) (hb : d85721 q = 1) : d11698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1673 q = 1) (hb : d85721 q = 1) : d11699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8948 q = 1) (hb : d125746 q = 1) : d126367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d125746, d126367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8948, d125746, d126367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1590 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d1590, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1591 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1591, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1592 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1592, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7034 q = 1) (hb : d125747 q = 1) : d126368 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d125747, d126368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7034, d125747, d126368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d8949 q = 1) (hb : d125748 q = 1) : d126369 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d125748, d126369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8949, d125748, d126369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d8950 q = 1) (hb : d125748 q = 1) : d126370 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d126370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8950, d126370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22729 (p : Pattern) (ha : d8956 p = 1) (hb : d125748 p = 1) : d126376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d125748 q = 1) : d126371 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22728 q ha hb
    | true =>
      simp only [d8951, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d125748 q = 1) : d126372 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22721 q ha hb
    | true =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d125748 q = 1) : d126373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d125748 q = 1) : d126374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d125748 q = 1) : d126375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8956 q = 1) (hb : d125748 q = 1) : d126376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d126376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d126376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22730 (p : Pattern) (ha : d8976 p = 1) (hb : d125748 p = 1) : d126382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d125748 q = 1) : d126379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d125748 q = 1) : d126380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d125748 q = 1) : d126381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d125748 q = 1) : d126382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d126382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d126382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22731 (p : Pattern) (ha : d94391 p = 1) (hb : d125748 p = 1) : d126388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d125748 q = 1) : d126357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22726 q ha hb
    | true =>
      simp only [d8938, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22724 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d125748 q = 1) : d126358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d125748 q = 1) : d126359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d125748 q = 1) : d126360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d125748 q = 1) : d126364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22727 q ha hb
    | true =>
      simp only [d8945, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22725 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d125748 q = 1) : d126365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d125748 q = 1) : d126366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d125748 q = 1) : d126377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22729 q ha hb
    | true =>
      simp only [d8961, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22722 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d125748 q = 1) : d126378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d125748 q = 1) : d126383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22730 q ha hb
    | true =>
      simp only [d8977, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d125748 q = 1) : d126384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d125748 q = 1) : d126385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d125748 q = 1) : d126386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d125748 q = 1) : d126387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94391 q = 1) (hb : d125748 q = 1) : d126388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d126388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d126388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22732 (p : Pattern) (ha : d1804 p = 1) (hb : d125748 p = 1) : d11755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d125748 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d125748 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d125748 q = 1) : d11755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22733 (p : Pattern) (ha : d1810 p = 1) (hb : d125748 p = 1) : d11761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d125748 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d125748 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d125748 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d125748 q = 1) : d11761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22734 (p : Pattern) (ha : d8983 p = 1) (hb : d125748 p = 1) : d126389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d125748 q = 1) : d126355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8983 q = 1) (hb : d125748 q = 1) : d126389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d126389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8983, d126389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22735 (p : Pattern) (ha : d8988 p = 1) (hb : d125748 p = 1) : d126394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d125748 q = 1) : d126361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d125748 q = 1) : d126362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8988 q = 1) (hb : d125748 q = 1) : d126394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d126394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8988, d126394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22736 (p : Pattern) (ha : d8992 p = 1) (hb : d125748 p = 1) : d126398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d125748 q = 1) : d126371 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22728 q ha hb
    | true =>
      simp only [d8951, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d125748 q = 1) : d126372 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22721 q ha hb
    | true =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d125748 q = 1) : d126373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d125748 q = 1) : d126374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d125748 q = 1) : d126375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8992 q = 1) (hb : d125748 q = 1) : d126398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d126398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8992, d126398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22737 (p : Pattern) (ha : d8993 p = 1) (hb : d125748 p = 1) : d126345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22721 q ha hb
    | true =>
      simp only [d7037, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d125748 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22708 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8993 q = 1) (hb : d125748 q = 1) : d126345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8993, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22738 (p : Pattern) (ha : d8998 p = 1) (hb : d125748 p = 1) : d126401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22716 q ha hb
    | true =>
      simp only [d8912, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d125748 q = 1) : d126379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d125748 q = 1) : d126380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d125748 q = 1) : d126381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d125748 q = 1) : d126401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d126401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d126401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22739 (p : Pattern) (ha : d94396 p = 1) (hb : d125748 p = 1) : d126407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d125748 q = 1) : d126357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22726 q ha hb
    | true =>
      simp only [d8938, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22724 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d125748 q = 1) : d126358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d125748 q = 1) : d126359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d125748 q = 1) : d126360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d125748 q = 1) : d126364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22727 q ha hb
    | true =>
      simp only [d8945, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22725 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d125748 q = 1) : d126365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d125748 q = 1) : d126366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d125748 q = 1) : d126377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22729 q ha hb
    | true =>
      simp only [d8961, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22722 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d125748 q = 1) : d126378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d125748 q = 1) : d126383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22730 q ha hb
    | true =>
      simp only [d8977, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d125748 q = 1) : d126384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d125748 q = 1) : d126385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d125748 q = 1) : d126386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d125748 q = 1) : d126387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8984 q = 1) (hb : d125748 q = 1) : d126390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d126390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22734 q ha hb
    | true =>
      simp only [d8984, d126390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22732 q ha hb
  have h16 (q : Pattern) (ha : d8985 q = 1) (hb : d125748 q = 1) : d126391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d126391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d126391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8986 q = 1) (hb : d125748 q = 1) : d126392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d126392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8986, d126392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8987 q = 1) (hb : d125748 q = 1) : d126393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d126393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d126393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8989 q = 1) (hb : d125748 q = 1) : d126395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d126395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22735 q ha hb
    | true =>
      simp only [d8989, d126395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22733 q ha hb
  have h20 (q : Pattern) (ha : d8990 q = 1) (hb : d125748 q = 1) : d126396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d126396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d126396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8991 q = 1) (hb : d125748 q = 1) : d126397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d126397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8991, d126397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8994 q = 1) (hb : d125748 q = 1) : d126399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22736 q ha hb
    | true =>
      simp only [d8994, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22737 q ha hb
  have h23 (q : Pattern) (ha : d94392 q = 1) (hb : d125748 q = 1) : d126400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94392, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8999 q = 1) (hb : d125748 q = 1) : d126402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22738 q ha hb
    | true =>
      simp only [d8999, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9000 q = 1) (hb : d125748 q = 1) : d126403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9000, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94393 q = 1) (hb : d125748 q = 1) : d126404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94393, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94394 q = 1) (hb : d125748 q = 1) : d126405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d126405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94394, d126405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94395 q = 1) (hb : d125748 q = 1) : d126406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d126406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94395, d126406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94396 q = 1) (hb : d125748 q = 1) : d126407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d126407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94396, d126407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22740 (p : Pattern) (ha : d94403 p = 1) (hb : d125748 p = 1) : d126416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d125748 q = 1) : d126399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22736 q ha hb
    | true =>
      simp only [d8994, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22737 q ha hb
  have h2 (q : Pattern) (ha : d94392 q = 1) (hb : d125748 q = 1) : d126400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94392, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8999 q = 1) (hb : d125748 q = 1) : d126402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22738 q ha hb
    | true =>
      simp only [d8999, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9000 q = 1) (hb : d125748 q = 1) : d126403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9000, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d125748 q = 1) : d126404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d125748 q = 1) : d126414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d126414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d126414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d125748 q = 1) : d126415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d126415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d126415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d125748 q = 1) : d126416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d126416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d126416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22741 (p : Pattern) (ha : d7082 p = 1) (hb : d125748 p = 1) : d126430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7080 q = 1) (hb : d125746 q = 1) : d126428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7080, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6495 q = 1) (hb : d94753 q = 1) : d6495 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6502 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6502, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d6503 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6503, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6504 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6504, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6505 q = 1) (hb : d125747 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6505, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d7081 q = 1) (hb : d125748 q = 1) : d126429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7081, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7082 q = 1) (hb : d125748 q = 1) : d126430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d7082, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22742 (p : Pattern) (ha : d9026 p = 1) (hb : d125748 p = 1) : d126425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1867 q = 1) : d1867 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1874 q = 1) (hb : d85721 q = 1) : d11805 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1875 q = 1) (hb : d85721 q = 1) : d11806 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1876 q = 1) (hb : d85721 q = 1) : d11807 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9024 q = 1) (hb : d125746 q = 1) : d126422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d125746, d126422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9024, d125746, d126422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1879 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d1879, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1880 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1880, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1881 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1881, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7080 q = 1) (hb : d125747 q = 1) : d126423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d125747, d126423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7080, d125747, d126423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d9025 q = 1) (hb : d125748 q = 1) : d126424 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d125748, d126424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9025, d125748, d126424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9026 q = 1) (hb : d125748 q = 1) : d126425 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d126425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9026, d126425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22743 (p : Pattern) (ha : d9032 p = 1) (hb : d125748 p = 1) : d126436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d125748 q = 1) : d126426 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d126426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22742 q ha hb
    | true =>
      simp only [d9027, d126426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d125748 q = 1) : d126427 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d126427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d126427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22741 q ha hb
    | true =>
      simp only [d7083, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d125748 q = 1) : d126433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d126433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, d126433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9030 q = 1) (hb : d125748 q = 1) : d126434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d126434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, d126434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9031 q = 1) (hb : d125748 q = 1) : d126435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d126435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9031, d126435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9032 q = 1) (hb : d125748 q = 1) : d126436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d126436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9032, d126436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22744 (p : Pattern) (ha : d9036 p = 1) (hb : d125748 p = 1) : d126440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22741 q ha hb
    | true =>
      simp only [d7083, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d125748 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22713 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d125748 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9033 q = 1) (hb : d125748 q = 1) : d126437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9034 q = 1) (hb : d125748 q = 1) : d126438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9034, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9035 q = 1) (hb : d125748 q = 1) : d126439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9035, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9036 q = 1) (hb : d125748 q = 1) : d126440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9036, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22745 (p : Pattern) (ha : d9050 p = 1) (hb : d125748 p = 1) : d126430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7080 q = 1) (hb : d125746 q = 1) : d126428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7080, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1889 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d1889, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1890 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1890, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1891 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1891, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1897 q = 1) (hb : d125747 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1897, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d9049 q = 1) (hb : d125748 q = 1) : d126429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9049, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9050 q = 1) (hb : d125748 q = 1) : d126430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9050, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22746 (p : Pattern) (ha : d9056 p = 1) (hb : d125748 p = 1) : d126446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22745 q ha hb
    | true =>
      simp only [d9051, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d125748 q = 1) : d126443 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d126443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d126443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d125748 q = 1) : d126444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d126444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d126444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d125748 q = 1) : d126445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d126445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d126445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d125748 q = 1) : d126446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d126446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d126446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22747 (p : Pattern) (ha : d94413 p = 1) (hb : d125748 p = 1) : d126452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d125748 q = 1) : d126441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d126441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22743 q ha hb
    | true =>
      simp only [d9037, d126441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22744 q ha hb
  have h2 (q : Pattern) (ha : d94409 q = 1) (hb : d125748 q = 1) : d126442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d126442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94409, d126442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9057 q = 1) (hb : d125748 q = 1) : d126447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d126447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22746 q ha hb
    | true =>
      simp only [d9057, d126447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9058 q = 1) (hb : d125748 q = 1) : d126448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d126448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9058, d126448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d125748 q = 1) : d126449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d126449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, d126449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d125748 q = 1) : d126450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d126450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d126450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d125748 q = 1) : d126451 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d126451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d126451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d125748 q = 1) : d126452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d126452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d126452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22748 (p : Pattern) (ha : d94419 p = 1) (hb : d125748 p = 1) : d126458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d125748 q = 1) : d126343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d126343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d126343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22718 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d125748 q = 1) : d126344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d126344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d126344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d125748 q = 1) : d126352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22718 q ha hb
    | true =>
      simp only [d8933, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22720 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d125748 q = 1) : d126353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d125748 q = 1) : d126354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d126354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d126354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94397 q = 1) (hb : d125748 q = 1) : d126408 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d126408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22731 q ha hb
    | true =>
      simp only [d94397, d126408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22739 q ha hb
  have h7 (q : Pattern) (ha : d9012 q = 1) (hb : d125748 q = 1) : d126410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d126410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22723 q ha hb
    | true =>
      simp only [d9012, d126410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22711 q ha hb
  have h8 (q : Pattern) (ha : d94398 q = 1) (hb : d125748 q = 1) : d126411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d126411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, d126411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94399 q = 1) (hb : d125748 q = 1) : d126412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d126412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94399, d126412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94400 q = 1) (hb : d125748 q = 1) : d126413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d126413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94400, d126413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94404 q = 1) (hb : d125748 q = 1) : d126417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d126417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94404, d126417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22740 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d125748 q = 1) : d11800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22712 q ha hb
  have h13 (q : Pattern) (ha : d94405 q = 1) (hb : d125748 q = 1) : d126418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d126418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94405, d126418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94406 q = 1) (hb : d125748 q = 1) : d126419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d126419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94406, d126419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94407 q = 1) (hb : d125748 q = 1) : d126420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d126420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94407, d126420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94408 q = 1) (hb : d125748 q = 1) : d126421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d126421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94408, d126421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94414 q = 1) (hb : d125748 q = 1) : d126453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d126453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94414, d126453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22747 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d125748 q = 1) : d11893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22715 q ha hb
  have h19 (q : Pattern) (ha : d94415 q = 1) (hb : d125748 q = 1) : d126454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d126454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94415, d126454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94416 q = 1) (hb : d125748 q = 1) : d126455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d126455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94416, d126455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94417 q = 1) (hb : d125748 q = 1) : d126456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d126456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94417, d126456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94418 q = 1) (hb : d125748 q = 1) : d126457 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d126457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94418, d126457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94419 q = 1) (hb : d125748 q = 1) : d126458 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d126458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94419, d126458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22749 (p : Pattern) (ha : d94425 p = 1) (hb : d125748 p = 1) : d126464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d125748 q = 1) : d126459 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d126459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d126459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22748 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d125748 q = 1) : d126460 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d126460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d126460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d125748 q = 1) : d126461 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d126461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d126461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d125748 q = 1) : d126462 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d126462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d126462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d125748 q = 1) : d126463 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d126463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d126463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d125748 q = 1) : d126464 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d126464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d126464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
