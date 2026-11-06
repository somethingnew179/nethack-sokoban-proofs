import NetHack.Soko22Hazard87.AndIntroBlocks0004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro1250 (p : Pattern) (ha : d1361 p = 1) (hb : d59441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1350 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1351 q = 1) (hb : d59427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d59427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1351, d59427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1352 q = 1) (hb : d59428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d59428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1352, d59428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1353 q = 1) (hb : d59429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d59429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1353, d59429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1354 q = 1) (hb : d59430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d59430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d59430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d59434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d59436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1356 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1357 q = 1) (hb : d59437 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d59437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1357, d59437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1358 q = 1) (hb : d59438 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d59438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1358, d59438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d1359 q = 1) (hb : d59439 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d59439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1359, d59439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1360 q = 1) (hb : d59440 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d59440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1360, d59440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1361 q = 1) (hb : d59441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d59441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1361, d59441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1251 (p : Pattern) (ha : d1370 p = 1) (hb : d59447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1356 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
    | true =>
      simp only [d1356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1357 q = 1) (hb : d59437 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d59437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d59437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1358 q = 1) (hb : d59438 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d59438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1358, d59438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1359 q = 1) (hb : d59445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d59445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d59445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1360 q = 1) (hb : d59446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d59446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d59446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1370 q = 1) (hb : d59447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d59447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d59447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1252 (p : Pattern) (ha : d1503 p = 1) (hb : d59456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1498 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q ha hb
    | true =>
      simp only [d1498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1499 q = 1) (hb : d59452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d59452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1499, d59452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1500 q = 1) (hb : d59453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d59453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1500, d59453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1501 q = 1) (hb : d59454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d59454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d59454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1502 q = 1) (hb : d59455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d59455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d59455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1503 q = 1) (hb : d59456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d59456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d59456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1253 (p : Pattern) (ha : d59431 p = 1) (hb : d59714 p = 1) : d59871 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d4968 q = 1) : d4968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59424 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d59426 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1350 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1351 q = 1) (hb : d59427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d59427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1351, d59427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d59428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d59428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1352, d59428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d59429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d59429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1353, d59429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d59430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d59430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1354, d59430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d59431 q = 1) (hb : d59714 q = 1) : d59871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59431, d59714, d59871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59431, d59714, d59871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro1254 (p : Pattern) (ha : d59461 p = 1) (hb : d59727 p = 1) : d59877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59442 q = 1) (hb : d59715 q = 1) : d59872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59442, d59715, d59872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1253 q ha hb
    | true =>
      simp only [d59442, d59715, d59872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1250 q hb ha
  have h3 (q : Pattern) (ha : d59442 q = 1) (hb : d59716 q = 1) : d59873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59716, d59873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59716, d59873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d59443 q = 1) (hb : d59717 q = 1) : d59874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59443, d59717, d59874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59443, d59717, d59874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d59444 q = 1) (hb : d59718 q = 1) : d59875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59444, d59718, d59875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59444, d59718, d59875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d59448 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1371 q = 1) (hb : d59448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d59448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1371, d59448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1251 q ha hb
  have h9 (q : Pattern) (ha : d59448 q = 1) (hb : d59719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d59449 q = 1) (hb : d59720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59449, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59449, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d59450 q = 1) (hb : d59721 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59450, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d59450, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d59451 q = 1) (hb : d59722 q = 1) : d59876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59451, d59722, d59876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59451, d59722, d59876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d59457 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1504 q = 1) (hb : d59457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d59457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1504, d59457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1252 q ha hb
  have h15 (q : Pattern) (ha : d59457 q = 1) (hb : d59723 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d59458 q = 1) (hb : d59724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59458, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d59458, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d59459 q = 1) (hb : d59725 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59459, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d59459, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d59460 q = 1) (hb : d59726 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59460, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d59460, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d59461 q = 1) (hb : d59727 q = 1) : d59877 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59461, d59727, d59877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d59461, d59727, d59877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1255 (p : Pattern) (ha : d59467 p = 1) (hb : d59733 p = 1) : d59883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59462 q = 1) (hb : d59728 q = 1) : d59878 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59462, d59728, d59878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59462, d59728, d59878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1254 q ha hb
  have h2 (q : Pattern) (ha : d59463 q = 1) (hb : d59729 q = 1) : d59879 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59463, d59729, d59879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59463, d59729, d59879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d59464 q = 1) (hb : d59730 q = 1) : d59880 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59464, d59730, d59880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59464, d59730, d59880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59465 q = 1) (hb : d59731 q = 1) : d59881 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59465, d59731, d59881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59465, d59731, d59881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59466 q = 1) (hb : d59732 q = 1) : d59882 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59466, d59732, d59882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59466, d59732, d59882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59467 q = 1) (hb : d59733 q = 1) : d59883 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59467, d59733, d59883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59467, d59733, d59883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1256 (p : Pattern) (ha : d1838 p = 1) (hb : d59503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1827 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1828 q = 1) (hb : d59489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d59489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1828, d59489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1829 q = 1) (hb : d59490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d59490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1829, d59490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1830 q = 1) (hb : d59491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d59491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1830, d59491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1831 q = 1) (hb : d59492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d59492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d59492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d59496 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d59498 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1833 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1834 q = 1) (hb : d59499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d59499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1834, d59499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1835 q = 1) (hb : d59500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d59500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1835, d59500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d1836 q = 1) (hb : d59501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d59501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1836, d59501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1837 q = 1) (hb : d59502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d59502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1837, d59502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1838 q = 1) (hb : d59503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d59503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1838, d59503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1257 (p : Pattern) (ha : d1847 p = 1) (hb : d59509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1833 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
    | true =>
      simp only [d1833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1834 q = 1) (hb : d59499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d59499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d59499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1835 q = 1) (hb : d59500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d59500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1835, d59500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1836 q = 1) (hb : d59507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d59507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d59507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1837 q = 1) (hb : d59508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d59508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d59508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1847 q = 1) (hb : d59509 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d59509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d59509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1258 (p : Pattern) (ha : d1980 p = 1) (hb : d59518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1975 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q ha hb
    | true =>
      simp only [d1975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1976 q = 1) (hb : d59514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d59514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1976, d59514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1977 q = 1) (hb : d59515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d59515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1977, d59515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1978 q = 1) (hb : d59516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d59516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d59516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1979 q = 1) (hb : d59517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d59517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d59517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1980 q = 1) (hb : d59518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d59518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d59518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1259 (p : Pattern) (ha : d59493 p = 1) (hb : d59737 p = 1) : d59887 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5079 q = 1) : d5079 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d59488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1827 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1828 q = 1) (hb : d59489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d59489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1828, d59489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d59490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d59490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1829, d59490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d59491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d59491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1830, d59491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d59492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d59492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1831, d59492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d59493 q = 1) (hb : d59737 q = 1) : d59887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59493, d59737, d59887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59493, d59737, d59887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro1260 (p : Pattern) (ha : d59523 p = 1) (hb : d59750 p = 1) : d59893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59504 q = 1) (hb : d59738 q = 1) : d59888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59504, d59738, d59888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1259 q ha hb
    | true =>
      simp only [d59504, d59738, d59888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1256 q hb ha
  have h3 (q : Pattern) (ha : d59504 q = 1) (hb : d59739 q = 1) : d59889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59739, d59889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59739, d59889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d59505 q = 1) (hb : d59740 q = 1) : d59890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59505, d59740, d59890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59505, d59740, d59890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d59506 q = 1) (hb : d59741 q = 1) : d59891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59506, d59741, d59891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59506, d59741, d59891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d59510 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1848 q = 1) (hb : d59510 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d59510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1848, d59510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1257 q ha hb
  have h9 (q : Pattern) (ha : d59510 q = 1) (hb : d59742 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d59511 q = 1) (hb : d59743 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59511, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59511, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d59512 q = 1) (hb : d59744 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59512, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d59512, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d59513 q = 1) (hb : d59745 q = 1) : d59892 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59513, d59745, d59892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59513, d59745, d59892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d59519 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1981 q = 1) (hb : d59519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d59519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1981, d59519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1258 q ha hb
  have h15 (q : Pattern) (ha : d59519 q = 1) (hb : d59746 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d59520 q = 1) (hb : d59747 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59520, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d59520, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d59521 q = 1) (hb : d59748 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59521, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d59521, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d59522 q = 1) (hb : d59749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59522, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d59522, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d59523 q = 1) (hb : d59750 q = 1) : d59893 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59523, d59750, d59893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d59523, d59750, d59893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1261 (p : Pattern) (ha : d59529 p = 1) (hb : d59756 p = 1) : d59899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59524 q = 1) (hb : d59751 q = 1) : d59894 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59524, d59751, d59894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59524, d59751, d59894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1260 q ha hb
  have h2 (q : Pattern) (ha : d59525 q = 1) (hb : d59752 q = 1) : d59895 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59525, d59752, d59895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59525, d59752, d59895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d59526 q = 1) (hb : d59753 q = 1) : d59896 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59526, d59753, d59896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59526, d59753, d59896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59527 q = 1) (hb : d59754 q = 1) : d59897 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59527, d59754, d59897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59527, d59754, d59897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59528 q = 1) (hb : d59755 q = 1) : d59898 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59528, d59755, d59898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59528, d59755, d59898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59529 q = 1) (hb : d59756 q = 1) : d59899 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59529, d59756, d59899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59529, d59756, d59899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1262 (p : Pattern) (ha : d2316 p = 1) (hb : d59566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59549 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2305 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2306 q = 1) (hb : d59552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d59552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2306, d59552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2307 q = 1) (hb : d59553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d59553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2307, d59553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2308 q = 1) (hb : d59554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d59554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2308, d59554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2309 q = 1) (hb : d59555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d59555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d59555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d59559 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d59561 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2311 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2312 q = 1) (hb : d59562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d59562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2312, d59562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2313 q = 1) (hb : d59563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d59563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2313, d59563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d2314 q = 1) (hb : d59564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d59564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2314, d59564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2315 q = 1) (hb : d59565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d59565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2315, d59565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2316 q = 1) (hb : d59566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d59566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2316, d59566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1263 (p : Pattern) (ha : d2325 p = 1) (hb : d59572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2311 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
    | true =>
      simp only [d2311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2312 q = 1) (hb : d59562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d59562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d59562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2313 q = 1) (hb : d59563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d59563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2313, d59563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2314 q = 1) (hb : d59570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d59570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d59570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2315 q = 1) (hb : d59571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d59571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d59571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2325 q = 1) (hb : d59572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d59572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d59572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1264 (p : Pattern) (ha : d2458 p = 1) (hb : d59581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2453 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q ha hb
    | true =>
      simp only [d2453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2454 q = 1) (hb : d59577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d59577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2454, d59577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2455 q = 1) (hb : d59578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d59578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2455, d59578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2456 q = 1) (hb : d59579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d59579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d59579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2457 q = 1) (hb : d59580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d59580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d59580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2458 q = 1) (hb : d59581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d59581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d59581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1265 (p : Pattern) (ha : d59556 p = 1) (hb : d59761 p = 1) : d59904 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5196 q = 1) : d5196 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d59551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2305 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2306 q = 1) (hb : d59552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d59552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2306, d59552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d59553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d59553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2307, d59553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d59554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d59554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2308, d59554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d59555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d59555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2309, d59555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d59556 q = 1) (hb : d59761 q = 1) : d59904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59556, d59761, d59904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59556, d59761, d59904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro1266 (p : Pattern) (ha : d59586 p = 1) (hb : d59774 p = 1) : d59910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d59567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59567 q = 1) (hb : d59762 q = 1) : d59905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59567, d59762, d59905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1265 q ha hb
    | true =>
      simp only [d59567, d59762, d59905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1262 q hb ha
  have h3 (q : Pattern) (ha : d59567 q = 1) (hb : d59763 q = 1) : d59906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59763, d59906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59763, d59906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d59568 q = 1) (hb : d59764 q = 1) : d59907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59568, d59764, d59907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59568, d59764, d59907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d59569 q = 1) (hb : d59765 q = 1) : d59908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59569, d59765, d59908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59569, d59765, d59908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d59573 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2326 q = 1) (hb : d59573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d59573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2326, d59573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1263 q ha hb
  have h9 (q : Pattern) (ha : d59573 q = 1) (hb : d59766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d59574 q = 1) (hb : d59767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59574, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59574, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d59575 q = 1) (hb : d59768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59575, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d59575, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d59576 q = 1) (hb : d59769 q = 1) : d59909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59576, d59769, d59909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59576, d59769, d59909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d59582 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2459 q = 1) (hb : d59582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d59582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2459, d59582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1264 q ha hb
  have h15 (q : Pattern) (ha : d59582 q = 1) (hb : d59770 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d59583 q = 1) (hb : d59771 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59583, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d59583, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d59584 q = 1) (hb : d59772 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59584, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d59584, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d59585 q = 1) (hb : d59773 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59585, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d59585, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d59586 q = 1) (hb : d59774 q = 1) : d59910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59586, d59774, d59910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d59586, d59774, d59910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro1267 (p : Pattern) (ha : d59592 p = 1) (hb : d59780 p = 1) : d59916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59587 q = 1) (hb : d59775 q = 1) : d59911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59587, d59775, d59911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59587, d59775, d59911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1266 q ha hb
  have h2 (q : Pattern) (ha : d59588 q = 1) (hb : d59776 q = 1) : d59912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59588, d59776, d59912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59588, d59776, d59912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d59589 q = 1) (hb : d59777 q = 1) : d59913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59589, d59777, d59913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59589, d59777, d59913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59590 q = 1) (hb : d59778 q = 1) : d59914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59590, d59778, d59914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59590, d59778, d59914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59591 q = 1) (hb : d59779 q = 1) : d59915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59591, d59779, d59915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59591, d59779, d59915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59592 q = 1) (hb : d59780 q = 1) : d59916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59592, d59780, d59916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59592, d59780, d59916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1268 (p : Pattern) (ha : d59598 p = 1) (hb : d59786 p = 1) : d59922 p = 1 := by
  have h0 (q : Pattern) (ha : d59347 q = 1) (hb : d59691 q = 1) : d59855 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59347, d59691, d59855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1237 q ha hb
    | true =>
      simp only [d59347, d59691, d59855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1243 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59407 q = 1) (hb : d59712 q = 1) : d59869 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59407, d59712, d59869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59407, d59712, d59869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1249 q ha hb
  have h3 (q : Pattern) (ha : d59408 q = 1) (hb : d59713 q = 1) : d59870 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59408, d59713, d59870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59408, d59713, d59870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59468 q = 1) (hb : d59734 q = 1) : d59884 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59468, d59734, d59884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59468, d59734, d59884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1255 q ha hb
  have h5 (q : Pattern) (ha : d59469 q = 1) (hb : d59735 q = 1) : d59885 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59469, d59735, d59885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59469, d59735, d59885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59470 q = 1) (hb : d59736 q = 1) : d59886 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59470, d59736, d59886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59470, d59736, d59886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59530 q = 1) (hb : d59757 q = 1) : d59900 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59530, d59757, d59900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59530, d59757, d59900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1261 q ha hb
  have h8 (q : Pattern) (ha : d59531 q = 1) (hb : d59758 q = 1) : d59901 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59531, d59758, d59901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59531, d59758, d59901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d59532 q = 1) (hb : d59759 q = 1) : d59902 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59532, d59759, d59902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59532, d59759, d59902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59533 q = 1) (hb : d59760 q = 1) : d59903 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59533, d59760, d59903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59533, d59760, d59903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d59593 q = 1) (hb : d59781 q = 1) : d59917 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59593, d59781, d59917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59593, d59781, d59917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1267 q ha hb
  have h12 (q : Pattern) (ha : d59594 q = 1) (hb : d59782 q = 1) : d59918 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59594, d59782, d59918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59594, d59782, d59918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59595 q = 1) (hb : d59783 q = 1) : d59919 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59595, d59783, d59919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59595, d59783, d59919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d59596 q = 1) (hb : d59784 q = 1) : d59920 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59596, d59784, d59920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59596, d59784, d59920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d59597 q = 1) (hb : d59785 q = 1) : d59921 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d59597, d59785, d59921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d59597, d59785, d59921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d59598 q = 1) (hb : d59786 q = 1) : d59922 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d59598, d59786, d59922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d59598, d59786, d59922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1269 (p : Pattern) (ha : d59604 p = 1) (hb : d59792 p = 1) : d59928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59599 q = 1) (hb : d59787 q = 1) : d59923 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d59599, d59787, d59923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1268 q ha hb
    | true =>
      simp only [d59599, d59787, d59923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59600 q = 1) (hb : d59788 q = 1) : d59924 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d59600, d59788, d59924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59600, d59788, d59924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59601 q = 1) (hb : d59789 q = 1) : d59925 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d59601, d59789, d59925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59601, d59789, d59925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59602 q = 1) (hb : d59790 q = 1) : d59926 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d59602, d59790, d59926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59602, d59790, d59926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59603 q = 1) (hb : d59791 q = 1) : d59927 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d59603, d59791, d59927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59603, d59791, d59927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59604 q = 1) (hb : d59792 q = 1) : d59928 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d59604, d59792, d59928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59604, d59792, d59928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1270 (p : Pattern) (ha : d59610 p = 1) (hb : d59798 p = 1) : d59934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59605 q = 1) (hb : d59793 q = 1) : d59929 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d59605, d59793, d59929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1269 q ha hb
    | true =>
      simp only [d59605, d59793, d59929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59606 q = 1) (hb : d59794 q = 1) : d59930 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d59606, d59794, d59930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59606, d59794, d59930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59607 q = 1) (hb : d59795 q = 1) : d59931 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d59607, d59795, d59931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59607, d59795, d59931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59608 q = 1) (hb : d59796 q = 1) : d59932 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d59608, d59796, d59932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59608, d59796, d59932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59609 q = 1) (hb : d59797 q = 1) : d59933 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d59609, d59797, d59933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59609, d59797, d59933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59610 q = 1) (hb : d59798 q = 1) : d59934 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d59610, d59798, d59934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59610, d59798, d59934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1271 (p : Pattern) (ha : d59616 p = 1) (hb : d59804 p = 1) : d59940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59611 q = 1) (hb : d59799 q = 1) : d59935 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d59611, d59799, d59935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1270 q ha hb
    | true =>
      simp only [d59611, d59799, d59935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59612 q = 1) (hb : d59800 q = 1) : d59936 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d59612, d59800, d59936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59612, d59800, d59936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59613 q = 1) (hb : d59801 q = 1) : d59937 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d59613, d59801, d59937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59613, d59801, d59937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59614 q = 1) (hb : d59802 q = 1) : d59938 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d59614, d59802, d59938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59614, d59802, d59938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59615 q = 1) (hb : d59803 q = 1) : d59939 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d59615, d59803, d59939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59615, d59803, d59939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59616 q = 1) (hb : d59804 q = 1) : d59940 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d59616, d59804, d59940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59616, d59804, d59940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1272 (p : Pattern) (ha : d59622 p = 1) (hb : d59810 p = 1) : d59946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59617 q = 1) (hb : d59805 q = 1) : d59941 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d59617, d59805, d59941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1271 q ha hb
    | true =>
      simp only [d59617, d59805, d59941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59618 q = 1) (hb : d59806 q = 1) : d59942 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d59618, d59806, d59942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59618, d59806, d59942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59619 q = 1) (hb : d59807 q = 1) : d59943 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d59619, d59807, d59943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59619, d59807, d59943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59620 q = 1) (hb : d59808 q = 1) : d59944 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d59620, d59808, d59944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59620, d59808, d59944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59621 q = 1) (hb : d59809 q = 1) : d59945 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d59621, d59809, d59945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59621, d59809, d59945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59622 q = 1) (hb : d59810 q = 1) : d59946 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d59622, d59810, d59946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59622, d59810, d59946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1273 (p : Pattern) (ha : d59628 p = 1) (hb : d59816 p = 1) : d59952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59623 q = 1) (hb : d59811 q = 1) : d59947 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d59623, d59811, d59947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1272 q ha hb
    | true =>
      simp only [d59623, d59811, d59947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59624 q = 1) (hb : d59812 q = 1) : d59948 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d59624, d59812, d59948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59624, d59812, d59948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59625 q = 1) (hb : d59813 q = 1) : d59949 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d59625, d59813, d59949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59625, d59813, d59949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59626 q = 1) (hb : d59814 q = 1) : d59950 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d59626, d59814, d59950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59626, d59814, d59950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59627 q = 1) (hb : d59815 q = 1) : d59951 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d59627, d59815, d59951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59627, d59815, d59951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59628 q = 1) (hb : d59816 q = 1) : d59952 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d59628, d59816, d59952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59628, d59816, d59952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1274 (p : Pattern) (ha : d59634 p = 1) (hb : d59822 p = 1) : d59958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59629 q = 1) (hb : d59817 q = 1) : d59953 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d59629, d59817, d59953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1273 q ha hb
    | true =>
      simp only [d59629, d59817, d59953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59630 q = 1) (hb : d59818 q = 1) : d59954 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d59630, d59818, d59954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59630, d59818, d59954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59631 q = 1) (hb : d59819 q = 1) : d59955 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d59631, d59819, d59955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59631, d59819, d59955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59632 q = 1) (hb : d59820 q = 1) : d59956 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d59632, d59820, d59956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59632, d59820, d59956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59633 q = 1) (hb : d59821 q = 1) : d59957 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d59633, d59821, d59957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59633, d59821, d59957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59634 q = 1) (hb : d59822 q = 1) : d59958 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d59634, d59822, d59958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59634, d59822, d59958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1275 (p : Pattern) (ha : d59640 p = 1) (hb : d59828 p = 1) : d59964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d59635 q = 1) (hb : d59823 q = 1) : d59959 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d59635, d59823, d59959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1274 q ha hb
    | true =>
      simp only [d59635, d59823, d59959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d59636 q = 1) (hb : d59824 q = 1) : d59960 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d59636, d59824, d59960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59636, d59824, d59960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d59637 q = 1) (hb : d59825 q = 1) : d59961 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d59637, d59825, d59961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d59637, d59825, d59961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d59638 q = 1) (hb : d59826 q = 1) : d59962 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d59638, d59826, d59962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59638, d59826, d59962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59639 q = 1) (hb : d59827 q = 1) : d59963 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d59639, d59827, d59963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59639, d59827, d59963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d59640 q = 1) (hb : d59828 q = 1) : d59964 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d59640, d59828, d59964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d59640, d59828, d59964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1276 (p : Pattern) (ha : d53647 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53637 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53638 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53639 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53639, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53640 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53641 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53642 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53643 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53643, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53644 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53645 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53646 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53647 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1277 (p : Pattern) (ha : d53671 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53653 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53654 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53656 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53657 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53657, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53658 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53659 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53660 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53666 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53667 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53667, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53668 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53669 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53670 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53671 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1278 (p : Pattern) (ha : d53677 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1276 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1277 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1279 (p : Pattern) (ha : d53697 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d509, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53678 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53679 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53681 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53682 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53682, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53683 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53684 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53685 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53692 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53693 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53693, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53694 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53695 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53696 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53697 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1280 (p : Pattern) (ha : d53703 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1279 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1281 (p : Pattern) (ha : d53724 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d801, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53705 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53706 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53709 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53709, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53710 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53711 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53712 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53719 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53720 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53720, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53721 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53722 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53723 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53724 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1282 (p : Pattern) (ha : d53730 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1281 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1283 (p : Pattern) (ha : d53752 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1179 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1180, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53733 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53734 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53736 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53737 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53737, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53738 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53739 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53740 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53747 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53748 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53748, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53749 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53750 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53751 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53752 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1284 (p : Pattern) (ha : d53758 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1283 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1285 (p : Pattern) (ha : d53781 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1640 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1641, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53762 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53763 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53765 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53766 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53766, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53767 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53768 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53769 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53776 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53777 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53777, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53778 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53779 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53780 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53781 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1286 (p : Pattern) (ha : d53787 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1285 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1287 (p : Pattern) (ha : d53811 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2124, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53792 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53793 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53795 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53796 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53796, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53797 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53798 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53799 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53806 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53807 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53807, d58749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d53808 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53809 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53810 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53811 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro1288 (p : Pattern) (ha : d53817 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1287 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1289 (p : Pattern) (ha : d53823 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1278 q ha hb
    | true =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1280 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1282 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1284 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1286 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1288 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1290 (p : Pattern) (ha : d53829 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1289 q ha hb
    | true =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1291 (p : Pattern) (ha : d53835 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1290 q ha hb
    | true =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1292 (p : Pattern) (ha : d53841 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1291 q ha hb
    | true =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1293 (p : Pattern) (ha : d53847 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1292 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1294 (p : Pattern) (ha : d53853 p = 1) (hb : d58749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1293 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1295 (p : Pattern) (ha : d53859 p = 1) (hb : d58750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1294 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d58749 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53858 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d58750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d58750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1296 (p : Pattern) (ha : d53865 p = 1) (hb : d58750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1295 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d58750 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1297 (p : Pattern) (ha : d0 p = 1) (hb : d59640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d59640 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro1298 (p : Pattern) (ha : d0 p = 1) (hb : d60238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60238 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro1299 (p : Pattern) (ha : d51865 p = 1) (hb : d54185 p = 1) : d54403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54185 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d54185 q = 1) : d54398 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d54398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro447 q ha hb
    | true =>
      simp only [d51860, d54398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d54185 q = 1) : d54399 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d54399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d54399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d54185 q = 1) : d54400 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d54400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d54400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d54185 q = 1) : d54401 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d54401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d54401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d54185 q = 1) : d54402 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d54402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d54402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d54185 q = 1) : d54403 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d54403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d54403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1300 (p : Pattern) (ha : d53865 p = 1) (hb : d54185 p = 1) : d54509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54185 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d54185 q = 1) : d54504 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d54504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro490 q ha hb
    | true =>
      simp only [d53860, d54504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d54185 q = 1) : d54505 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d54505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d54505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d54185 q = 1) : d54506 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d54506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d54506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d54185 q = 1) : d54507 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d54507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d54507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d54185 q = 1) : d54508 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d54508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d54508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d54185 q = 1) : d54509 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d54509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d54509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1301 (p : Pattern) (ha : d95 p = 1) (hb : d60240 p = 1) : d60448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d65 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94 q = 1) (hb : d54517 q = 1) : d94 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d95 q = 1) (hb : d60240 q = 1) : d60448 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d60240, d60448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d95, d60240, d60448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1302 (p : Pattern) (ha : d51652 p = 1) (hb : d60240 p = 1) : d60453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51651 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4364 q = 1) (hb : d54517 q = 1) : d4364 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51652 q = 1) (hb : d60240 q = 1) : d60453 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d60240, d60453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51652, d60240, d60453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1303 (p : Pattern) (ha : d51676 p = 1) (hb : d60240 p = 1) : d60459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51671 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51675 q = 1) (hb : d54517 q = 1) : d51675 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51676 q = 1) (hb : d60240 q = 1) : d60459 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51676, d60240, d60459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51676, d60240, d60459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1304 (p : Pattern) (ha : d51682 p = 1) (hb : d60240 p = 1) : d60465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d60240 q = 1) : d60449 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d60449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d60449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1301 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d60240 q = 1) : d60450 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d60450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d60450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d60240 q = 1) : d60451 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d60451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d60451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d60240 q = 1) : d60452 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d60452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d60452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d60240 q = 1) : d60454 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d60454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d60454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1302 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d60240 q = 1) : d60455 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d60455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d60455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d60240 q = 1) : d60456 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d60456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d60456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d60240 q = 1) : d60457 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d60457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d60457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d60240 q = 1) : d60458 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d60458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d60458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51677 q = 1) (hb : d60240 q = 1) : d60460 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51677, d60460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51677, d60460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1303 q ha hb
  have h11 (q : Pattern) (ha : d51678 q = 1) (hb : d60240 q = 1) : d60461 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51678, d60461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51678, d60461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51679 q = 1) (hb : d60240 q = 1) : d60462 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51679, d60462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51679, d60462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51680 q = 1) (hb : d60240 q = 1) : d60463 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51680, d60463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51680, d60463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51681 q = 1) (hb : d60240 q = 1) : d60464 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51681, d60464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51681, d60464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51682 q = 1) (hb : d60240 q = 1) : d60465 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51682, d60465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51682, d60465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1305 (p : Pattern) (ha : d51701 p = 1) (hb : d60240 p = 1) : d60466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51696 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51700 q = 1) (hb : d54517 q = 1) : d51700 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51701 q = 1) (hb : d60240 q = 1) : d60466 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51701, d60240, d60466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51701, d60240, d60466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1306 (p : Pattern) (ha : d51707 p = 1) (hb : d60240 p = 1) : d60472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51702 q = 1) (hb : d60240 q = 1) : d60467 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51702, d60467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51702, d60467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1305 q ha hb
  have h2 (q : Pattern) (ha : d51703 q = 1) (hb : d60240 q = 1) : d60468 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51703, d60468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51703, d60468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51704 q = 1) (hb : d60240 q = 1) : d60469 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51704, d60469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51704, d60469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51705 q = 1) (hb : d60240 q = 1) : d60470 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51705, d60470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51705, d60470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51706 q = 1) (hb : d60240 q = 1) : d60471 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51706, d60471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51706, d60471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51707 q = 1) (hb : d60240 q = 1) : d60472 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51707, d60472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51707, d60472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1307 (p : Pattern) (ha : d51727 p = 1) (hb : d60240 p = 1) : d60474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51722 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51726 q = 1) (hb : d54517 q = 1) : d51726 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51727 q = 1) (hb : d60240 q = 1) : d60474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51727, d60240, d60474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51727, d60240, d60474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1308 (p : Pattern) (ha : d51733 p = 1) (hb : d60240 p = 1) : d60480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51728 q = 1) (hb : d60240 q = 1) : d60475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51728, d60475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51728, d60475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1307 q ha hb
  have h2 (q : Pattern) (ha : d51729 q = 1) (hb : d60240 q = 1) : d60476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51729, d60476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51729, d60476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51730 q = 1) (hb : d60240 q = 1) : d60477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51730, d60477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51730, d60477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51731 q = 1) (hb : d60240 q = 1) : d60478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51731, d60478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51731, d60478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51732 q = 1) (hb : d60240 q = 1) : d60479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51732, d60479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51732, d60479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51733 q = 1) (hb : d60240 q = 1) : d60480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51733, d60480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51733, d60480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1309 (p : Pattern) (ha : d51754 p = 1) (hb : d60240 p = 1) : d60483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51753 q = 1) (hb : d54517 q = 1) : d51753 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51754 q = 1) (hb : d60240 q = 1) : d60483 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51754, d60240, d60483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51754, d60240, d60483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1310 (p : Pattern) (ha : d51760 p = 1) (hb : d60240 p = 1) : d60489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51755 q = 1) (hb : d60240 q = 1) : d60484 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51755, d60484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51755, d60484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1309 q ha hb
  have h2 (q : Pattern) (ha : d51756 q = 1) (hb : d60240 q = 1) : d60485 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51756, d60485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51756, d60485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51757 q = 1) (hb : d60240 q = 1) : d60486 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51757, d60486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51757, d60486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51758 q = 1) (hb : d60240 q = 1) : d60487 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51758, d60487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51758, d60487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51759 q = 1) (hb : d60240 q = 1) : d60488 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51759, d60488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51759, d60488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51760 q = 1) (hb : d60240 q = 1) : d60489 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51760, d60489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51760, d60489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1311 (p : Pattern) (ha : d51782 p = 1) (hb : d60240 p = 1) : d60493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51781 q = 1) (hb : d54517 q = 1) : d51781 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51782 q = 1) (hb : d60240 q = 1) : d60493 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51782, d60240, d60493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51782, d60240, d60493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1312 (p : Pattern) (ha : d51788 p = 1) (hb : d60240 p = 1) : d60499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51783 q = 1) (hb : d60240 q = 1) : d60494 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51783, d60494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51783, d60494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1311 q ha hb
  have h2 (q : Pattern) (ha : d51784 q = 1) (hb : d60240 q = 1) : d60495 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51784, d60495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51784, d60495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51785 q = 1) (hb : d60240 q = 1) : d60496 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51785, d60496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51785, d60496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51786 q = 1) (hb : d60240 q = 1) : d60497 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51786, d60497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51786, d60497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51787 q = 1) (hb : d60240 q = 1) : d60498 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51787, d60498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51787, d60498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51788 q = 1) (hb : d60240 q = 1) : d60499 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51788, d60499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51788, d60499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1313 (p : Pattern) (ha : d51811 p = 1) (hb : d60240 p = 1) : d60504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51806 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51810 q = 1) (hb : d54517 q = 1) : d51810 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51811 q = 1) (hb : d60240 q = 1) : d60504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51811, d60240, d60504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51811, d60240, d60504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1314 (p : Pattern) (ha : d51817 p = 1) (hb : d60240 p = 1) : d60510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51812 q = 1) (hb : d60240 q = 1) : d60505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51812, d60505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51812, d60505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1313 q ha hb
  have h2 (q : Pattern) (ha : d51813 q = 1) (hb : d60240 q = 1) : d60506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51813, d60506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51813, d60506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51814 q = 1) (hb : d60240 q = 1) : d60507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51814, d60507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51814, d60507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51815 q = 1) (hb : d60240 q = 1) : d60508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51815, d60508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51815, d60508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51816 q = 1) (hb : d60240 q = 1) : d60509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51816, d60509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51816, d60509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51817 q = 1) (hb : d60240 q = 1) : d60510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51817, d60510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51817, d60510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1315 (p : Pattern) (ha : d51823 p = 1) (hb : d60240 p = 1) : d60516 p = 1 := by
  have h0 (q : Pattern) (ha : d51708 q = 1) (hb : d60240 q = 1) : d60473 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51708, d60473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1304 q ha hb
    | true =>
      simp only [d51708, d60473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1306 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51734 q = 1) (hb : d60240 q = 1) : d60481 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51734, d60481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51734, d60481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1308 q ha hb
  have h3 (q : Pattern) (ha : d51735 q = 1) (hb : d60240 q = 1) : d60482 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51735, d60482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51735, d60482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51761 q = 1) (hb : d60240 q = 1) : d60490 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51761, d60490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51761, d60490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1310 q ha hb
  have h5 (q : Pattern) (ha : d51762 q = 1) (hb : d60240 q = 1) : d60491 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51762, d60491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51762, d60491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51763 q = 1) (hb : d60240 q = 1) : d60492 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51763, d60492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51763, d60492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51789 q = 1) (hb : d60240 q = 1) : d60500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51789, d60500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51789, d60500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1312 q ha hb
  have h8 (q : Pattern) (ha : d51790 q = 1) (hb : d60240 q = 1) : d60501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51790, d60501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51790, d60501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51791 q = 1) (hb : d60240 q = 1) : d60502 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51791, d60502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51791, d60502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51792 q = 1) (hb : d60240 q = 1) : d60503 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51792, d60503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51792, d60503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51818 q = 1) (hb : d60240 q = 1) : d60511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51818, d60511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51818, d60511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1314 q ha hb
  have h12 (q : Pattern) (ha : d51819 q = 1) (hb : d60240 q = 1) : d60512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51819, d60512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51819, d60512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51820 q = 1) (hb : d60240 q = 1) : d60513 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51820, d60513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51820, d60513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51821 q = 1) (hb : d60240 q = 1) : d60514 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51821, d60514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51821, d60514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51822 q = 1) (hb : d60240 q = 1) : d60515 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d51822, d60515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51822, d60515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51823 q = 1) (hb : d60240 q = 1) : d60516 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d51823, d60516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51823, d60516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1316 (p : Pattern) (ha : d51829 p = 1) (hb : d60240 p = 1) : d60522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51824 q = 1) (hb : d60240 q = 1) : d60517 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d51824, d60517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1315 q ha hb
    | true =>
      simp only [d51824, d60517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51825 q = 1) (hb : d60240 q = 1) : d60518 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d51825, d60518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51825, d60518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51826 q = 1) (hb : d60240 q = 1) : d60519 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d51826, d60519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51826, d60519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51827 q = 1) (hb : d60240 q = 1) : d60520 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d51827, d60520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51827, d60520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51828 q = 1) (hb : d60240 q = 1) : d60521 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d51828, d60521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51828, d60521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51829 q = 1) (hb : d60240 q = 1) : d60522 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d51829, d60522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51829, d60522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1317 (p : Pattern) (ha : d51835 p = 1) (hb : d60240 p = 1) : d60528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51830 q = 1) (hb : d60240 q = 1) : d60523 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d51830, d60523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1316 q ha hb
    | true =>
      simp only [d51830, d60523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51831 q = 1) (hb : d60240 q = 1) : d60524 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d51831, d60524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51831, d60524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51832 q = 1) (hb : d60240 q = 1) : d60525 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d51832, d60525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51832, d60525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51833 q = 1) (hb : d60240 q = 1) : d60526 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d51833, d60526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51833, d60526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51834 q = 1) (hb : d60240 q = 1) : d60527 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d51834, d60527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51834, d60527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51835 q = 1) (hb : d60240 q = 1) : d60528 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d51835, d60528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51835, d60528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1318 (p : Pattern) (ha : d51841 p = 1) (hb : d60240 p = 1) : d60534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51836 q = 1) (hb : d60240 q = 1) : d60529 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d51836, d60529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1317 q ha hb
    | true =>
      simp only [d51836, d60529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51837 q = 1) (hb : d60240 q = 1) : d60530 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d51837, d60530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51837, d60530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51838 q = 1) (hb : d60240 q = 1) : d60531 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d51838, d60531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51838, d60531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51839 q = 1) (hb : d60240 q = 1) : d60532 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d51839, d60532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51839, d60532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51840 q = 1) (hb : d60240 q = 1) : d60533 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d51840, d60533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51840, d60533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51841 q = 1) (hb : d60240 q = 1) : d60534 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d51841, d60534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51841, d60534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1319 (p : Pattern) (ha : d51847 p = 1) (hb : d60240 p = 1) : d60540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51842 q = 1) (hb : d60240 q = 1) : d60535 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d51842, d60535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1318 q ha hb
    | true =>
      simp only [d51842, d60535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51843 q = 1) (hb : d60240 q = 1) : d60536 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d51843, d60536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51843, d60536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51844 q = 1) (hb : d60240 q = 1) : d60537 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d51844, d60537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51844, d60537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51845 q = 1) (hb : d60240 q = 1) : d60538 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d51845, d60538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51845, d60538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51846 q = 1) (hb : d60240 q = 1) : d60539 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d51846, d60539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51846, d60539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51847 q = 1) (hb : d60240 q = 1) : d60540 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d51847, d60540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51847, d60540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1320 (p : Pattern) (ha : d51853 p = 1) (hb : d60240 p = 1) : d60546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51848 q = 1) (hb : d60240 q = 1) : d60541 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d51848, d60541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1319 q ha hb
    | true =>
      simp only [d51848, d60541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51849 q = 1) (hb : d60240 q = 1) : d60542 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d51849, d60542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51849, d60542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51850 q = 1) (hb : d60240 q = 1) : d60543 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d51850, d60543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51850, d60543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51851 q = 1) (hb : d60240 q = 1) : d60544 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d51851, d60544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51851, d60544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51852 q = 1) (hb : d60240 q = 1) : d60545 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d51852, d60545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51852, d60545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51853 q = 1) (hb : d60240 q = 1) : d60546 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d51853, d60546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51853, d60546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1321 (p : Pattern) (ha : d51859 p = 1) (hb : d60241 p = 1) : d60552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51854 q = 1) (hb : d60240 q = 1) : d60547 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d51854, d60547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1320 q ha hb
    | true =>
      simp only [d51854, d60547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51855 q = 1) (hb : d60240 q = 1) : d60548 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d51855, d60548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51855, d60548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51856 q = 1) (hb : d60240 q = 1) : d60549 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d51856, d60549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51856, d60549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51857 q = 1) (hb : d60240 q = 1) : d60550 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d51857, d60550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51857, d60550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51858 q = 1) (hb : d60241 q = 1) : d60551 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d51858, d60241, d60551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51858, d60241, d60551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d60241 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51859 q = 1) (hb : d60241 q = 1) : d60552 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d51859, d60552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51859, d60552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1322 (p : Pattern) (ha : d51865 p = 1) (hb : d60241 p = 1) : d60558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60241 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d60241 q = 1) : d60553 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d60553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1321 q ha hb
    | true =>
      simp only [d51860, d60553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d60241 q = 1) : d60554 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d60554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d60554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d60241 q = 1) : d60555 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d60555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d60555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d60241 q = 1) : d60556 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d60556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d60556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d60241 q = 1) : d60557 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d60557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d60557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d60241 q = 1) : d60558 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d60558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d60558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1323 (p : Pattern) (ha : d71 p = 1) (hb : d51882 p = 1) : d17564 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d67 q = 1) : d67 q = 1 := by
    exact hb
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
  have h4 (q : Pattern) (ha : d68 q = 1) (hb : d51879 q = 1) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69 q = 1) (hb : d51880 q = 1) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d70 q = 1) (hb : d51881 q = 1) : d17563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51881, d17563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70, d51881, d17563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d71 q = 1) (hb : d51882 q = 1) : d17564 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d51882, d17564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71, d51882, d17564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro1324 (p : Pattern) (ha : d77 p = 1) (hb : d51888 p = 1) : d17570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d51883 q = 1) : d17565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
    | true =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d51884 q = 1) : d17566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d51885 q = 1) : d17567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d51886 q = 1) : d17568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51886, d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d51886, d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d51887 q = 1) : d17569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d51887, d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, d51887, d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d51888 q = 1) : d17570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, d51888, d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, d51888, d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1325 (p : Pattern) (ha : d83 p = 1) (hb : d51901 p = 1) : d17576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d51889 q = 1) : d17571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51889, d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1324 q ha hb
    | true =>
      simp only [d78, d51889, d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d51890 q = 1) : d17572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51890, d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51890, d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d51891 q = 1) : d17573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, d51891, d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, d51891, d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d51892 q = 1) : d17574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, d51892, d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, d51892, d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d51893 q = 1) : d17575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, d51893, d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, d51893, d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d51901 q = 1) : d17576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, d51901, d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, d51901, d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1326 (p : Pattern) (ha : d89 p = 1) (hb : d51912 p = 1) : d17582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d51902 q = 1) : d17577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
    | true =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d51903 q = 1) : d17578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51903, d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, d51903, d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d51904 q = 1) : d17579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, d51904, d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, d51904, d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d51905 q = 1) : d17580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, d51905, d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, d51905, d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d51906 q = 1) : d17581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, d51906, d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, d51906, d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d51912 q = 1) : d17582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, d51912, d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, d51912, d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1327 (p : Pattern) (ha : d51916 p = 1) (hb : d60448 p = 1) : d17588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51916 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d90 q = 1) (hb : d51913 q = 1) : d17583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d51913, d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d90, d51913, d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1326 q ha hb
  have h3 (q : Pattern) (ha : d91 q = 1) (hb : d51914 q = 1) : d17584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d51914, d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d91, d51914, d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d92 q = 1) (hb : d51915 q = 1) : d17585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, d51915, d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92, d51915, d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d93 q = 1) (hb : d51916 q = 1) : d17586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, d51916, d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93, d51916, d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d94 q = 1) (hb : d51916 q = 1) : d17587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94, d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51916 q = 1) (hb : d60448 q = 1) : d17588 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60448, d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60448, d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro1328 (p : Pattern) (ha : d231 p = 1) (hb : d51995 p = 1) : d17596 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d227 q = 1) : d227 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d228 q = 1) (hb : d51992 q = 1) : d17593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d229 q = 1) (hb : d51993 q = 1) : d17594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d67 q = 1) : d67 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d68 q = 1) (hb : d51879 q = 1) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69 q = 1) (hb : d51880 q = 1) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d230 q = 1) (hb : d51994 q = 1) : d17595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d51994, d17595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d230, d51994, d17595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70 q = 1) (hb : d51881 q = 1) : d17563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51881, d17563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70, d51881, d17563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d231 q = 1) (hb : d51995 q = 1) : d17596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d51995, d17596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231, d51995, d17596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1329 (p : Pattern) (ha : d237 p = 1) (hb : d52001 p = 1) : d17602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d51996 q = 1) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
    | true =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d51997 q = 1) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d51998 q = 1) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51883 q = 1) : d17565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
    | true =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51884 q = 1) : d17566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51885 q = 1) : d17567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d51999 q = 1) : d17600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d51999, d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d51999, d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51886 q = 1) : d17568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51886, d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51886, d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d52000 q = 1) : d17601 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d52000, d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d52000, d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237 q = 1) (hb : d52001 q = 1) : d17602 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d52001, d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237, d52001, d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1330 (p : Pattern) (ha : d243 p = 1) (hb : d52023 p = 1) : d17608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d52002 q = 1) : d17603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52002, d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1329 q ha hb
    | true =>
      simp only [d238, d52002, d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d52003 q = 1) : d17604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d52003, d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d52003, d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51889 q = 1) : d17571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51889, d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1324 q ha hb
    | true =>
      simp only [d78, d51889, d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51890 q = 1) : d17572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51890, d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51890, d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d52004 q = 1) : d17605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d52004, d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d52004, d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d52005 q = 1) : d17606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d52005, d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d52005, d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d52006 q = 1) : d17607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d52006, d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d52006, d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d52023 q = 1) : d17608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d52023, d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d52023, d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1331 (p : Pattern) (ha : d4359 p = 1) (hb : d52038 p = 1) : d60563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d52024 q = 1) : d17609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52024, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1330 q ha hb
    | true =>
      simp only [d244, d52024, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d52025 q = 1) : d60559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d52025, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d52025, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51902 q = 1) : d17577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
    | true =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51903 q = 1) : d17578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51903, d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51903, d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4356 q = 1) (hb : d52026 q = 1) : d60560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d52026, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d52026, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4357 q = 1) (hb : d52036 q = 1) : d60561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d52036, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d52036, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4358 q = 1) (hb : d52037 q = 1) : d60562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d52037, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d52037, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4359 q = 1) (hb : d52038 q = 1) : d60563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d52038, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d52038, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1332 (p : Pattern) (ha : d52042 p = 1) (hb : d60453 p = 1) : d60569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4360 q = 1) (hb : d52039 q = 1) : d60564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d52039, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4360, d52039, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1331 q ha hb
  have h3 (q : Pattern) (ha : d4361 q = 1) (hb : d52040 q = 1) : d60565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d52040, d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4361, d52040, d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d4362 q = 1) (hb : d52041 q = 1) : d60566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d52041, d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4362, d52041, d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4363 q = 1) (hb : d52042 q = 1) : d60567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d52042, d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4363, d52042, d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d4364 q = 1) (hb : d52042 q = 1) : d60568 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4364, d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52042 q = 1) (hb : d60453 q = 1) : d60569 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60453, d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60453, d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro1333 (p : Pattern) (ha : d462 p = 1) (hb : d52172 p = 1) : d17696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d51902 q = 1) : d17577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
    | true =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d51959 q = 1) : d17692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d51959, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, d51959, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d51960 q = 1) : d17693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d51960, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, d51960, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d51961 q = 1) : d17694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d51961, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d51961, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d51962 q = 1) : d17695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d51962, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d51962, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d52172 q = 1) : d17696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d52172, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d52172, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1334 (p : Pattern) (ha : d417 p = 1) (hb : d52123 p = 1) : d60575 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d413 q = 1) : d413 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d414 q = 1) (hb : d52120 q = 1) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d415 q = 1) (hb : d52121 q = 1) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d227 q = 1) : d227 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d228 q = 1) (hb : d51992 q = 1) : d17593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d229 q = 1) (hb : d51993 q = 1) : d17594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d416 q = 1) (hb : d52122 q = 1) : d17645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d52122, d17645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d416, d52122, d17645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d67 q = 1) : d67 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d68 q = 1) (hb : d51879 q = 1) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d68, d51879, d17561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69 q = 1) (hb : d51880 q = 1) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69, d51880, d17562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d230 q = 1) (hb : d51994 q = 1) : d17595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d51994, d17595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d230, d51994, d17595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d417 q = 1) (hb : d52123 q = 1) : d60575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d52123, d60575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d417, d52123, d60575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1335 (p : Pattern) (ha : d423 p = 1) (hb : d52129 p = 1) : d60581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52124 q = 1) : d60576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1334 q ha hb
    | true =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52125 q = 1) : d60577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52126 q = 1) : d60578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d51996 q = 1) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
    | true =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d51997 q = 1) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d51998 q = 1) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52127 q = 1) : d60579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51883 q = 1) : d17565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
    | true =>
      simp only [d72, d51883, d17565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51884 q = 1) : d17566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51884, d17566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51885 q = 1) : d17567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51885, d17567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d51999 q = 1) : d17600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d51999, d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d51999, d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d422 q = 1) (hb : d52128 q = 1) : d60580 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d52128, d60580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d422, d52128, d60580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d423 q = 1) (hb : d52129 q = 1) : d60581 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d52129, d60581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d423, d52129, d60581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1336 (p : Pattern) (ha : d429 p = 1) (hb : d52153 p = 1) : d60587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d52130 q = 1) : d60582 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d52130, d60582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1335 q ha hb
    | true =>
      simp only [d424, d52130, d60582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d52131 q = 1) : d60583 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d52131, d60583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d52131, d60583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d52002 q = 1) : d17603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52002, d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1329 q ha hb
    | true =>
      simp only [d238, d52002, d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d52003 q = 1) : d17604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d52003, d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d52003, d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d426 q = 1) (hb : d52132 q = 1) : d60584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d52132, d60584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d426, d52132, d60584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d52133 q = 1) : d60585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d52133, d60585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d427, d52133, d60585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d52134 q = 1) : d60586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d52134, d60586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d52134, d60586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d52153 q = 1) : d60587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d52153, d60587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d52153, d60587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1337 (p : Pattern) (ha : d4395 p = 1) (hb : d52170 p = 1) : d60595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d52154 q = 1) : d60588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d52154, d60588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1336 q ha hb
    | true =>
      simp only [d430, d52154, d60588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1330 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4391 q = 1) (hb : d52155 q = 1) : d60589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d52155, d60589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d52155, d60589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d451 q = 1) (hb : d52156 q = 1) : d60590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52156, d60590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1330 q ha hb
    | true =>
      simp only [d451, d52156, d60590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d452 q = 1) (hb : d52157 q = 1) : d60591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52157, d60591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d452, d52157, d60591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4392 q = 1) (hb : d52158 q = 1) : d60592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d52158, d60592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4392, d52158, d60592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4393 q = 1) (hb : d52168 q = 1) : d60593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d52168, d60593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d52168, d60593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4394 q = 1) (hb : d52169 q = 1) : d60594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d52169, d60594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d52169, d60594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4395 q = 1) (hb : d52170 q = 1) : d60595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d52170, d60595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d52170, d60595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1338 (p : Pattern) (ha : d52176 p = 1) (hb : d60459 p = 1) : d60601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4396 q = 1) (hb : d52171 q = 1) : d60596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d52171, d60596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4396, d52171, d60596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1337 q ha hb
  have h3 (q : Pattern) (ha : d463 q = 1) (hb : d52173 q = 1) : d17697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52173, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d463, d52173, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1333 q ha hb
  have h4 (q : Pattern) (ha : d51672 q = 1) (hb : d52174 q = 1) : d60597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51672, d52174, d60597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51672, d52174, d60597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51673 q = 1) (hb : d52175 q = 1) : d60598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51673, d52175, d60598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51673, d52175, d60598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51674 q = 1) (hb : d52176 q = 1) : d60599 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51674, d52176, d60599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51674, d52176, d60599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51675 q = 1) (hb : d52176 q = 1) : d60600 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51675, d60600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51675, d60600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52176 q = 1) (hb : d60459 q = 1) : d60601 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60459, d60601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60459, d60601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1339 (p : Pattern) (ha : d60359 p = 1) (hb : d60465 p = 1) : d60607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60345 q = 1) (hb : d60449 q = 1) : d17589 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60345, d60449, d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60345, d60449, d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1327 q ha hb
  have h2 (q : Pattern) (ha : d60346 q = 1) (hb : d60450 q = 1) : d17590 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60346, d60450, d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60346, d60450, d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60347 q = 1) (hb : d60451 q = 1) : d17591 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60347, d60451, d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60347, d60451, d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60348 q = 1) (hb : d60452 q = 1) : d17592 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60348, d60452, d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60348, d60452, d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60349 q = 1) (hb : d60454 q = 1) : d60570 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60349, d60454, d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60349, d60454, d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1332 q ha hb
  have h6 (q : Pattern) (ha : d60350 q = 1) (hb : d60455 q = 1) : d60571 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60350, d60455, d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60350, d60455, d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60351 q = 1) (hb : d60456 q = 1) : d60572 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60351, d60456, d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60351, d60456, d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60352 q = 1) (hb : d60457 q = 1) : d60573 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60352, d60457, d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60352, d60457, d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60353 q = 1) (hb : d60458 q = 1) : d60574 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60353, d60458, d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60353, d60458, d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d60354 q = 1) (hb : d60460 q = 1) : d60602 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60354, d60460, d60602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60354, d60460, d60602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1338 q ha hb
  have h11 (q : Pattern) (ha : d60355 q = 1) (hb : d60461 q = 1) : d60603 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60355, d60461, d60603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60355, d60461, d60603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d60356 q = 1) (hb : d60462 q = 1) : d60604 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60356, d60462, d60604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60356, d60462, d60604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d60357 q = 1) (hb : d60463 q = 1) : d60605 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60357, d60463, d60605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60357, d60463, d60605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d60358 q = 1) (hb : d60464 q = 1) : d60606 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60358, d60464, d60606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60358, d60464, d60606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d60359 q = 1) (hb : d60465 q = 1) : d60607 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60359, d60465, d60607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d60359, d60465, d60607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1340 (p : Pattern) (ha : d683 p = 1) (hb : d52228 p = 1) : d17740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d51996 q = 1) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
    | true =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d51997 q = 1) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d51998 q = 1) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d52222 q = 1) : d17730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52222, d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52222, d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d52227 q = 1) : d17739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d52227, d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d52227, d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d683 q = 1) (hb : d52228 q = 1) : d17740 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d52228, d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d683, d52228, d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1341 (p : Pattern) (ha : d730 p = 1) (hb : d52248 p = 1) : d17792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d52229 q = 1) : d17741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52229, d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1340 q ha hb
    | true =>
      simp only [d684, d52229, d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d52230 q = 1) : d17742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52230, d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52230, d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d52235 q = 1) : d17789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d52235, d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d52235, d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d52236 q = 1) : d17790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d52236, d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d52236, d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d52237 q = 1) : d17791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d52237, d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d52237, d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d52248 q = 1) : d17792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d52248, d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d52248, d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1342 (p : Pattern) (ha : d736 p = 1) (hb : d52357 p = 1) : d17798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d52343 q = 1) : d17793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d52343, d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1341 q ha hb
    | true =>
      simp only [d731, d52343, d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d52344 q = 1) : d17794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d52344, d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d52344, d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d52345 q = 1) : d17795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d52345, d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d52345, d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d52346 q = 1) : d17796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d52346, d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d52346, d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d52347 q = 1) : d17797 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d52347, d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d52347, d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d52357 q = 1) : d17798 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d52357, d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d52357, d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1343 (p : Pattern) (ha : d664 p = 1) (hb : d52295 p = 1) : d60609 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d660 q = 1) : d660 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d661 q = 1) (hb : d52292 q = 1) : d17709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d662 q = 1) (hb : d52293 q = 1) : d17710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d413 q = 1) : d413 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d414 q = 1) (hb : d52120 q = 1) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d415 q = 1) (hb : d52121 q = 1) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d663 q = 1) (hb : d52294 q = 1) : d60608 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d227 q = 1) : d227 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d228 q = 1) (hb : d51992 q = 1) : d17593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d228, d51992, d17593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d229 q = 1) (hb : d51993 q = 1) : d17594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d229, d51993, d17594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d416 q = 1) (hb : d52122 q = 1) : d17645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d52122, d17645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d416, d52122, d17645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d664 q = 1) (hb : d52295 q = 1) : d60609 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d52295, d60609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d664, d52295, d60609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1344 (p : Pattern) (ha : d670 p = 1) (hb : d52301 p = 1) : d60615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d52296 q = 1) : d60610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52296, d60610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1343 q ha hb
    | true =>
      simp only [d665, d52296, d60610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1334 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d52297 q = 1) : d60611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52297, d60611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d52297, d60611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d52298 q = 1) : d60612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52298, d60612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d52298, d60612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d418 q = 1) (hb : d52124 q = 1) : d60576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1334 q ha hb
    | true =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
  have h5 (q : Pattern) (ha : d419 q = 1) (hb : d52125 q = 1) : d60577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d420 q = 1) (hb : d52126 q = 1) : d60578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d668 q = 1) (hb : d52299 q = 1) : d60613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d52299, d60613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d668, d52299, d60613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d232 q = 1) (hb : d51996 q = 1) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
    | true =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
  have h9 (q : Pattern) (ha : d233 q = 1) (hb : d51997 q = 1) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d234 q = 1) (hb : d51998 q = 1) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d421 q = 1) (hb : d52127 q = 1) : d60579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d669 q = 1) (hb : d52300 q = 1) : d60614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d52300, d60614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d669, d52300, d60614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d670 q = 1) (hb : d52301 q = 1) : d60615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d52301, d60615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d670, d52301, d60615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1345 (p : Pattern) (ha : d675 p = 1) (hb : d52224 p = 1) : d60619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52124 q = 1) : d60576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1334 q ha hb
    | true =>
      simp only [d418, d52124, d60576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52125 q = 1) : d60577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52125, d60577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52126 q = 1) : d60578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52126, d60578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d51996 q = 1) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1328 q ha hb
    | true =>
      simp only [d232, d51996, d17597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1323 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d51997 q = 1) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d51997, d17598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d51998 q = 1) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d51998, d17599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52127 q = 1) : d60579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52127, d60579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d52222 q = 1) : d17730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52222, d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d52222, d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d674 q = 1) (hb : d52223 q = 1) : d60618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d52223, d60618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d674, d52223, d60618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d675 q = 1) (hb : d52224 q = 1) : d60619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d52224, d60619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d675, d52224, d60619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1346 (p : Pattern) (ha : d681 p = 1) (hb : d52327 p = 1) : d60625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d52302 q = 1) : d60616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d52302, d60616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1344 q ha hb
    | true =>
      simp only [d671, d52302, d60616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d52303 q = 1) : d60617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d52303, d60617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d52303, d60617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d676 q = 1) (hb : d52225 q = 1) : d60620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d52225, d60620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1345 q ha hb
    | true =>
      simp only [d676, d52225, d60620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d677 q = 1) (hb : d52226 q = 1) : d60621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d52226, d60621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d52226, d60621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d678 q = 1) (hb : d52304 q = 1) : d60622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d52304, d60622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d678, d52304, d60622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d679 q = 1) (hb : d52305 q = 1) : d60623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d52305, d60623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d679, d52305, d60623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d680 q = 1) (hb : d52306 q = 1) : d60624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d52306, d60624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d680, d52306, d60624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d681 q = 1) (hb : d52327 q = 1) : d60625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d52327, d60625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d681, d52327, d60625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1347 (p : Pattern) (ha : d689 p = 1) (hb : d52247 p = 1) : d60629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d52225 q = 1) : d60620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d52225, d60620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1345 q ha hb
    | true =>
      simp only [d676, d52225, d60620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d52226 q = 1) : d60621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d52226, d60621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d52226, d60621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52229 q = 1) : d17741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52229, d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1340 q ha hb
    | true =>
      simp only [d684, d52229, d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52230 q = 1) : d17742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52230, d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52230, d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d686 q = 1) (hb : d52231 q = 1) : d60626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d52231, d60626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d52231, d60626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d687 q = 1) (hb : d52232 q = 1) : d60627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d52232, d60627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d687, d52232, d60627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d688 q = 1) (hb : d52233 q = 1) : d60628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d52233, d60628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d688, d52233, d60628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d689 q = 1) (hb : d52247 q = 1) : d60629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d52247, d60629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d689, d52247, d60629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1348 (p : Pattern) (ha : d4432 p = 1) (hb : d52355 p = 1) : d60637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d690 q = 1) (hb : d52328 q = 1) : d60630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d52328, d60630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1346 q ha hb
    | true =>
      simp only [d690, d52328, d60630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1347 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4428 q = 1) (hb : d52329 q = 1) : d60631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d52329, d60631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4428, d52329, d60631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d720 q = 1) (hb : d52330 q = 1) : d60632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d52330, d60632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1347 q ha hb
    | true =>
      simp only [d720, d52330, d60632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d721 q = 1) (hb : d52331 q = 1) : d60633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d52331, d60633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d721, d52331, d60633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4429 q = 1) (hb : d52332 q = 1) : d60634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d52332, d60634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4429, d52332, d60634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4430 q = 1) (hb : d52353 q = 1) : d60635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d52353, d60635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d52353, d60635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4431 q = 1) (hb : d52354 q = 1) : d60636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d52354, d60636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d52354, d60636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4432 q = 1) (hb : d52355 q = 1) : d60637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d52355, d60637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d52355, d60637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1349 (p : Pattern) (ha : d52361 p = 1) (hb : d60466 p = 1) : d60643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4433 q = 1) (hb : d52356 q = 1) : d60638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d52356, d60638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4433, d52356, d60638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1348 q ha hb
  have h3 (q : Pattern) (ha : d737 q = 1) (hb : d52358 q = 1) : d17799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52358, d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d737, d52358, d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1342 q ha hb
  have h4 (q : Pattern) (ha : d51697 q = 1) (hb : d52359 q = 1) : d60639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51697, d52359, d60639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51697, d52359, d60639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51698 q = 1) (hb : d52360 q = 1) : d60640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51698, d52360, d60640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51698, d52360, d60640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51699 q = 1) (hb : d52361 q = 1) : d60641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51699, d52361, d60641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51699, d52361, d60641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51700 q = 1) (hb : d52361 q = 1) : d60642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51700, d60642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51700, d60642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52361 q = 1) (hb : d60466 q = 1) : d60643 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60466, d60643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60466, d60643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1350 (p : Pattern) (ha : d60365 p = 1) (hb : d60472 p = 1) : d60649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60360 q = 1) (hb : d60467 q = 1) : d60644 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60360, d60467, d60644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60360, d60467, d60644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1349 q ha hb
  have h2 (q : Pattern) (ha : d60361 q = 1) (hb : d60468 q = 1) : d60645 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60361, d60468, d60645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60361, d60468, d60645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60362 q = 1) (hb : d60469 q = 1) : d60646 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60362, d60469, d60646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60362, d60469, d60646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60363 q = 1) (hb : d60470 q = 1) : d60647 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60363, d60470, d60647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60363, d60470, d60647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60364 q = 1) (hb : d60471 q = 1) : d60648 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60364, d60471, d60648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60364, d60471, d60648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60365 q = 1) (hb : d60472 q = 1) : d60649 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60365, d60472, d60649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60365, d60472, d60649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1351 (p : Pattern) (ha : d981 p = 1) (hb : d52435 p = 1) : d17835 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d413 q = 1) : d413 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d414 q = 1) (hb : d52120 q = 1) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d415 q = 1) (hb : d52121 q = 1) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d972 q = 1) : d972 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d973 q = 1) (hb : d52430 q = 1) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d974 q = 1) (hb : d52431 q = 1) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d975 q = 1) (hb : d52432 q = 1) : d17834 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52432, d17834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d975, d52432, d17834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d980 q = 1) (hb : d52434 q = 1) : d17828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52434, d17828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d980, d52434, d17828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d981 q = 1) (hb : d52435 q = 1) : d17835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d52435, d17835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d981, d52435, d17835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1352 (p : Pattern) (ha : d986 p = 1) (hb : d52439 p = 1) : d17839 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d972 q = 1) : d972 q = 1 := by
    exact hb
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
  have h4 (q : Pattern) (ha : d973 q = 1) (hb : d52430 q = 1) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d974 q = 1) (hb : d52431 q = 1) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d980 q = 1) (hb : d52434 q = 1) : d17828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52434, d17828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d980, d52434, d17828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d986 q = 1) (hb : d52439 q = 1) : d17839 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d52439, d17839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d986, d52439, d17839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro1353 (p : Pattern) (ha : d1005 p = 1) (hb : d52450 p = 1) : d17858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d52440 q = 1) : d17840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1351 q ha hb
    | true =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1352 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d52441 q = 1) : d17841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d52442 q = 1) : d17842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d52444 q = 1) : d17848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52444, d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d52444, d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d52449 q = 1) : d17857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d52449, d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d52449, d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d52450 q = 1) : d17858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d52450, d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d52450, d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1354 (p : Pattern) (ha : d1063 p = 1) (hb : d52470 p = 1) : d17921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d52451 q = 1) : d17859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52451, d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1353 q ha hb
    | true =>
      simp only [d1006, d52451, d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d52452 q = 1) : d17860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52452, d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52452, d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d52457 q = 1) : d17918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d52457, d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d52457, d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d52458 q = 1) : d17919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d52458, d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d52458, d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d52459 q = 1) : d17920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d52459, d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d52459, d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d52470 q = 1) : d17921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d52470, d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d52470, d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1355 (p : Pattern) (ha : d1069 p = 1) (hb : d52578 p = 1) : d17927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d52564 q = 1) : d17922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d52564, d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1354 q ha hb
    | true =>
      simp only [d1064, d52564, d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d52565 q = 1) : d17923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d52565, d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d52565, d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d52566 q = 1) : d17924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d52566, d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d52566, d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d52567 q = 1) : d17925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d52567, d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d52567, d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d52568 q = 1) : d17926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d52568, d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d52568, d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d52578 q = 1) : d17927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d52578, d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d52578, d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1356 (p : Pattern) (ha : d970 p = 1) (hb : d52516 p = 1) : d60652 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d966 q = 1) : d966 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d967 q = 1) (hb : d52513 q = 1) : d17812 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52513, d17812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d967, d52513, d17812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d968 q = 1) (hb : d52514 q = 1) : d17813 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52514, d17813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d968, d52514, d17813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d660 q = 1) : d660 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d661 q = 1) (hb : d52292 q = 1) : d17709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d662 q = 1) (hb : d52293 q = 1) : d17710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d969 q = 1) (hb : d52515 q = 1) : d60651 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d52515, d60651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d969, d52515, d60651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d413 q = 1) : d413 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d414 q = 1) (hb : d52120 q = 1) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d415 q = 1) (hb : d52121 q = 1) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d663 q = 1) (hb : d52294 q = 1) : d60608 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d970 q = 1) (hb : d52516 q = 1) : d60652 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d52516, d60652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d970, d52516, d60652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1357 (p : Pattern) (ha : d976 p = 1) (hb : d52433 p = 1) : d60653 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d660 q = 1) : d660 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d661 q = 1) (hb : d52292 q = 1) : d17709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d661, d52292, d17709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d662 q = 1) (hb : d52293 q = 1) : d17710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d662, d52293, d17710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d413 q = 1) : d413 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d414 q = 1) (hb : d52120 q = 1) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d414, d52120, d17643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d415 q = 1) (hb : d52121 q = 1) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d415, d52121, d17644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d663 q = 1) (hb : d52294 q = 1) : d60608 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d663, d52294, d60608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d972 q = 1) : d972 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d973 q = 1) (hb : d52430 q = 1) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d973, d52430, d17821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d974 q = 1) (hb : d52431 q = 1) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d974, d52431, d17822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d975 q = 1) (hb : d52432 q = 1) : d17834 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52432, d17834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d975, d52432, d17834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d976 q = 1) (hb : d52433 q = 1) : d60653 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d52433, d60653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d976, d52433, d60653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1358 (p : Pattern) (ha : d992 p = 1) (hb : d52522 p = 1) : d60663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d52517 q = 1) : d60654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52517, d60654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1356 q ha hb
    | true =>
      simp only [d977, d52517, d60654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1357 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d52518 q = 1) : d60655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52518, d60655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d52518, d60655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d52519 q = 1) : d60656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52519, d60656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d52519, d60656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d982 q = 1) (hb : d52436 q = 1) : d60657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52436, d60657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1357 q ha hb
    | true =>
      simp only [d982, d52436, d60657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1351 q ha hb
  have h5 (q : Pattern) (ha : d983 q = 1) (hb : d52437 q = 1) : d60658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52437, d60658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52437, d60658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d984 q = 1) (hb : d52438 q = 1) : d60659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52438, d60659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52438, d60659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d985 q = 1) (hb : d52520 q = 1) : d60660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d52520, d60660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d985, d52520, d60660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d52440 q = 1) : d17840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1351 q ha hb
    | true =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1352 q ha hb
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d52441 q = 1) : d17841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d52442 q = 1) : d17842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d52443 q = 1) : d60661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d52443, d60661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d990, d52443, d60661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d991 q = 1) (hb : d52521 q = 1) : d60662 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d52521, d60662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d991, d52521, d60662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d992 q = 1) (hb : d52522 q = 1) : d60663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d52522, d60663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d992, d52522, d60663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1359 (p : Pattern) (ha : d997 p = 1) (hb : d52446 p = 1) : d60667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52436 q = 1) : d60657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52436, d60657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1357 q ha hb
    | true =>
      simp only [d982, d52436, d60657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1351 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52437 q = 1) : d60658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52437, d60658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52437, d60658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52438 q = 1) : d60659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52438, d60659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52438, d60659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d52440 q = 1) : d17840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1351 q ha hb
    | true =>
      simp only [d987, d52440, d17840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1352 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d52441 q = 1) : d17841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52441, d17841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d52442 q = 1) : d17842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52442, d17842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d990 q = 1) (hb : d52443 q = 1) : d60661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d52443, d60661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d52443, d60661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d52444 q = 1) : d17848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52444, d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d52444, d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d996 q = 1) (hb : d52445 q = 1) : d60666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d52445, d60666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d996, d52445, d60666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d997 q = 1) (hb : d52446 q = 1) : d60667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d52446, d60667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d997, d52446, d60667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1360 (p : Pattern) (ha : d1003 p = 1) (hb : d52548 p = 1) : d60673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d52523 q = 1) : d60664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d52523, d60664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1358 q ha hb
    | true =>
      simp only [d993, d52523, d60664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d52524 q = 1) : d60665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d52524, d60665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d52524, d60665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d998 q = 1) (hb : d52447 q = 1) : d60668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d52447, d60668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1359 q ha hb
    | true =>
      simp only [d998, d52447, d60668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d999 q = 1) (hb : d52448 q = 1) : d60669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d52448, d60669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d52448, d60669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1000 q = 1) (hb : d52525 q = 1) : d60670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d52525, d60670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1000, d52525, d60670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1001 q = 1) (hb : d52526 q = 1) : d60671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d52526, d60671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1001, d52526, d60671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1002 q = 1) (hb : d52527 q = 1) : d60672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d52527, d60672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1002, d52527, d60672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1003 q = 1) (hb : d52548 q = 1) : d60673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d52548, d60673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1003, d52548, d60673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1361 (p : Pattern) (ha : d1011 p = 1) (hb : d52469 p = 1) : d60677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d52447 q = 1) : d60668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d52447, d60668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1359 q ha hb
    | true =>
      simp only [d998, d52447, d60668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d52448 q = 1) : d60669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d52448, d60669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d52448, d60669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52451 q = 1) : d17859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52451, d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1353 q ha hb
    | true =>
      simp only [d1006, d52451, d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52452 q = 1) : d17860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52452, d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52452, d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d52453 q = 1) : d60674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d52453, d60674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d52453, d60674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d52454 q = 1) : d60675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d52454, d60675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, d52454, d60675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d52455 q = 1) : d60676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d52455, d60676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d52455, d60676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d52469 q = 1) : d60677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d52469, d60677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d52469, d60677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1362 (p : Pattern) (ha : d4470 p = 1) (hb : d52576 p = 1) : d60685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d52549 q = 1) : d60678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d52549, d60678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1360 q ha hb
    | true =>
      simp only [d1012, d52549, d60678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d52550 q = 1) : d60679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d52550, d60679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d52550, d60679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1053 q = 1) (hb : d52551 q = 1) : d60680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d52551, d60680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1361 q ha hb
    | true =>
      simp only [d1053, d52551, d60680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1054 q = 1) (hb : d52552 q = 1) : d60681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d52552, d60681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1054, d52552, d60681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4467 q = 1) (hb : d52553 q = 1) : d60682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d52553, d60682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4467, d52553, d60682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4468 q = 1) (hb : d52574 q = 1) : d60683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d52574, d60683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d52574, d60683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4469 q = 1) (hb : d52575 q = 1) : d60684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d52575, d60684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d52575, d60684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4470 q = 1) (hb : d52576 q = 1) : d60685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d52576, d60685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d52576, d60685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1363 (p : Pattern) (ha : d52582 p = 1) (hb : d60474 p = 1) : d60691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4471 q = 1) (hb : d52577 q = 1) : d60686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d52577, d60686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4471, d52577, d60686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1362 q ha hb
  have h3 (q : Pattern) (ha : d1070 q = 1) (hb : d52579 q = 1) : d17928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52579, d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1070, d52579, d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1355 q ha hb
  have h4 (q : Pattern) (ha : d51723 q = 1) (hb : d52580 q = 1) : d60687 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51723, d52580, d60687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51723, d52580, d60687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51724 q = 1) (hb : d52581 q = 1) : d60688 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51724, d52581, d60688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51724, d52581, d60688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51725 q = 1) (hb : d52582 q = 1) : d60689 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51725, d52582, d60689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51725, d52582, d60689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51726 q = 1) (hb : d52582 q = 1) : d60690 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51726, d60690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51726, d60690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52582 q = 1) (hb : d60474 q = 1) : d60691 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60474, d60691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60474, d60691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1364 (p : Pattern) (ha : d60372 p = 1) (hb : d60480 p = 1) : d60697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60367 q = 1) (hb : d60475 q = 1) : d60692 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60367, d60475, d60692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60367, d60475, d60692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1363 q ha hb
  have h2 (q : Pattern) (ha : d60368 q = 1) (hb : d60476 q = 1) : d60693 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60368, d60476, d60693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60368, d60476, d60693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60369 q = 1) (hb : d60477 q = 1) : d60694 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60369, d60477, d60694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60369, d60477, d60694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60370 q = 1) (hb : d60478 q = 1) : d60695 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60370, d60478, d60695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60370, d60478, d60695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60371 q = 1) (hb : d60479 q = 1) : d60696 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60371, d60479, d60696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60371, d60479, d60696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60372 q = 1) (hb : d60480 q = 1) : d60697 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60372, d60480, d60697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60372, d60480, d60697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1365 (p : Pattern) (ha : d1401 p = 1) (hb : d52709 p = 1) : d60707 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1386 q = 1) : d1386 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1387 q = 1) (hb : d52693 q = 1) : d17974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1388 q = 1) (hb : d52694 q = 1) : d17975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1392 q = 1) : d1392 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1393 q = 1) (hb : d52704 q = 1) : d17976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1394 q = 1) (hb : d52705 q = 1) : d17977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1395 q = 1) (hb : d52706 q = 1) : d17978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d52706, d17978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1395, d52706, d17978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1400 q = 1) (hb : d52708 q = 1) : d18007 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d52708, d18007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1400, d52708, d18007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1401 q = 1) (hb : d52709 q = 1) : d60707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d52709, d60707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1401, d52709, d60707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1366 (p : Pattern) (ha : d1411 p = 1) (hb : d52722 p = 1) : d60715 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1392 q = 1) : d1392 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1393 q = 1) (hb : d52704 q = 1) : d17976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1394 q = 1) (hb : d52705 q = 1) : d17977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1400 q = 1) (hb : d52708 q = 1) : d18007 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d52708, d18007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1400, d52708, d18007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1407 q = 1) : d1407 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d1136 q = 1) (hb : d52717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, d52717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro154 q ha hb
    | true =>
      simp only [d1136, d52717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1137 q = 1) (hb : d52718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, d52718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1137, d52718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1408 q = 1) (hb : d52719 q = 1) : d60712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1408, d52719, d60712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1408, d52719, d60712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1409 q = 1) (hb : d52720 q = 1) : d60713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1409, d52720, d60713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1409, d52720, d60713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1410 q = 1) (hb : d52721 q = 1) : d60714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1410, d52721, d60714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1410, d52721, d60714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1411 q = 1) (hb : d52722 q = 1) : d60715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1411, d52722, d60715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1411, d52722, d60715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1367 (p : Pattern) (ha : d1430 p = 1) (hb : d52733 p = 1) : d60734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d52723 q = 1) : d60716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1365 q ha hb
    | true =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1366 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d52724 q = 1) : d60717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d52725 q = 1) : d60718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1420 q = 1) (hb : d52727 q = 1) : d60724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d52727, d60724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d52727, d60724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1429 q = 1) (hb : d52732 q = 1) : d60733 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d52732, d60733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1429, d52732, d60733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1430 q = 1) (hb : d52733 q = 1) : d60734 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d52733, d60734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1430, d52733, d60734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1368 (p : Pattern) (ha : d1497 p = 1) (hb : d52753 p = 1) : d60753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d52734 q = 1) : d60735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52734, d60735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1367 q ha hb
    | true =>
      simp only [d1431, d52734, d60735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d52735 q = 1) : d60736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52735, d60736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52735, d60736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d52740 q = 1) : d60750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d52740, d60750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d52740, d60750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d52741 q = 1) : d60751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d52741, d60751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d52741, d60751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d52742 q = 1) : d60752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d52742, d60752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d52742, d60752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d52753 q = 1) : d60753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d52753, d60753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d52753, d60753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1369 (p : Pattern) (ha : d1503 p = 1) (hb : d52858 p = 1) : d60759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d52844 q = 1) : d60754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d52844, d60754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1368 q ha hb
    | true =>
      simp only [d1498, d52844, d60754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d52845 q = 1) : d60755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d52845, d60755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d52845, d60755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d52846 q = 1) : d60756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d52846, d60756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d52846, d60756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d52847 q = 1) : d60757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d52847, d60757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d52847, d60757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d52848 q = 1) : d60758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d52848, d60758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d52848, d60758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d52858 q = 1) : d60759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d52858, d60759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d52858, d60759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1370 (p : Pattern) (ha : d1390 p = 1) (hb : d52796 p = 1) : d60702 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1377 q = 1) : d1377 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1378 q = 1) (hb : d52793 q = 1) : d17942 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52793, d17942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1378, d52793, d17942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1379 q = 1) (hb : d52794 q = 1) : d17943 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d52794, d17943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1379, d52794, d17943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1381 q = 1) : d1381 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1382 q = 1) (hb : d52683 q = 1) : d17953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52683, d17953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1382, d52683, d17953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1383 q = 1) (hb : d52684 q = 1) : d17954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52684, d17954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1383, d52684, d17954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1384 q = 1) (hb : d52795 q = 1) : d60700 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d52795, d60700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1384, d52795, d60700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1386 q = 1) : d1386 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1387 q = 1) (hb : d52693 q = 1) : d17974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1388 q = 1) (hb : d52694 q = 1) : d17975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1389 q = 1) (hb : d52695 q = 1) : d60701 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d52695, d60701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1389, d52695, d60701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1390 q = 1) (hb : d52796 q = 1) : d60702 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d52796, d60702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1390, d52796, d60702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1371 (p : Pattern) (ha : d1396 p = 1) (hb : d52707 p = 1) : d60703 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1381 q = 1) : d1381 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1382 q = 1) (hb : d52683 q = 1) : d17953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52683, d17953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1382, d52683, d17953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1383 q = 1) (hb : d52684 q = 1) : d17954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52684, d17954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1383, d52684, d17954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1386 q = 1) : d1386 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1387 q = 1) (hb : d52693 q = 1) : d17974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1387, d52693, d17974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1388 q = 1) (hb : d52694 q = 1) : d17975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1388, d52694, d17975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1389 q = 1) (hb : d52695 q = 1) : d60701 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d52695, d60701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1389, d52695, d60701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1392 q = 1) : d1392 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1393 q = 1) (hb : d52704 q = 1) : d17976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1393, d52704, d17976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1394 q = 1) (hb : d52705 q = 1) : d17977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1394, d52705, d17977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1395 q = 1) (hb : d52706 q = 1) : d17978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d52706, d17978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1395, d52706, d17978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1396 q = 1) (hb : d52707 q = 1) : d60703 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d52707, d60703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1396, d52707, d60703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1372 (p : Pattern) (ha : d1417 p = 1) (hb : d52802 p = 1) : d60721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d52797 q = 1) : d60704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52797, d60704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1370 q ha hb
    | true =>
      simp only [d1397, d52797, d60704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1371 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d52798 q = 1) : d60705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52798, d60705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d52798, d60705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d52799 q = 1) : d60706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52799, d60706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d52799, d60706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1402 q = 1) (hb : d52710 q = 1) : d60708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52710, d60708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1371 q ha hb
    | true =>
      simp only [d1402, d52710, d60708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1365 q ha hb
  have h5 (q : Pattern) (ha : d1403 q = 1) (hb : d52711 q = 1) : d60709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52711, d60709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52711, d60709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1404 q = 1) (hb : d52712 q = 1) : d60710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52712, d60710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52712, d60710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1405 q = 1) (hb : d52800 q = 1) : d60711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d52800, d60711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1405, d52800, d60711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1412 q = 1) (hb : d52723 q = 1) : d60716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1365 q ha hb
    | true =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1366 q ha hb
  have h9 (q : Pattern) (ha : d1413 q = 1) (hb : d52724 q = 1) : d60717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1414 q = 1) (hb : d52725 q = 1) : d60718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1415 q = 1) (hb : d52726 q = 1) : d60719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d52726, d60719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1415, d52726, d60719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1416 q = 1) (hb : d52801 q = 1) : d60720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d52801, d60720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1416, d52801, d60720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1417 q = 1) (hb : d52802 q = 1) : d60721 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d52802, d60721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1417, d52802, d60721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1373 (p : Pattern) (ha : d1422 p = 1) (hb : d52729 p = 1) : d60726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52710 q = 1) : d60708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52710, d60708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1371 q ha hb
    | true =>
      simp only [d1402, d52710, d60708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1365 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52711 q = 1) : d60709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52711, d60709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52711, d60709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52712 q = 1) : d60710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52712, d60710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52712, d60710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d52723 q = 1) : d60716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1365 q ha hb
    | true =>
      simp only [d1412, d52723, d60716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1366 q ha hb
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d52724 q = 1) : d60717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52724, d60717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d52725 q = 1) : d60718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52725, d60718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1415 q = 1) (hb : d52726 q = 1) : d60719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d52726, d60719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d52726, d60719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1420 q = 1) (hb : d52727 q = 1) : d60724 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d52727, d60724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1420, d52727, d60724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1421 q = 1) (hb : d52728 q = 1) : d60725 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d52728, d60725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1421, d52728, d60725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1422 q = 1) (hb : d52729 q = 1) : d60726 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d52729, d60726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1422, d52729, d60726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1374 (p : Pattern) (ha : d1428 p = 1) (hb : d52828 p = 1) : d60732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d52803 q = 1) : d60722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d52803, d60722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1372 q ha hb
    | true =>
      simp only [d1418, d52803, d60722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d52804 q = 1) : d60723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d52804, d60723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d52804, d60723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1423 q = 1) (hb : d52730 q = 1) : d60727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d52730, d60727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1373 q ha hb
    | true =>
      simp only [d1423, d52730, d60727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1424 q = 1) (hb : d52731 q = 1) : d60728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d52731, d60728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d52731, d60728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1425 q = 1) (hb : d52805 q = 1) : d60729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d52805, d60729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1425, d52805, d60729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1426 q = 1) (hb : d52806 q = 1) : d60730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d52806, d60730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1426, d52806, d60730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1427 q = 1) (hb : d52807 q = 1) : d60731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d52807, d60731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1427, d52807, d60731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1428 q = 1) (hb : d52828 q = 1) : d60732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d52828, d60732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1428, d52828, d60732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1375 (p : Pattern) (ha : d1436 p = 1) (hb : d52752 p = 1) : d60740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d52730 q = 1) : d60727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d52730, d60727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1373 q ha hb
    | true =>
      simp only [d1423, d52730, d60727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d52731 q = 1) : d60728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d52731, d60728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d52731, d60728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52734 q = 1) : d60735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52734, d60735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1367 q ha hb
    | true =>
      simp only [d1431, d52734, d60735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52735 q = 1) : d60736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52735, d60736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52735, d60736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d52736 q = 1) : d60737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d52736, d60737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d52736, d60737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d52737 q = 1) : d60738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d52737, d60738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, d52737, d60738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d52738 q = 1) : d60739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d52738, d60739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d52738, d60739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d52752 q = 1) : d60740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d52752, d60740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d52752, d60740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1376 (p : Pattern) (ha : d4509 p = 1) (hb : d52856 p = 1) : d60748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d52829 q = 1) : d60741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d52829, d60741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1374 q ha hb
    | true =>
      simp only [d1437, d52829, d60741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1375 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d52830 q = 1) : d60742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d52830, d60742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d52830, d60742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1487 q = 1) (hb : d52831 q = 1) : d60743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d52831, d60743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1375 q ha hb
    | true =>
      simp only [d1487, d52831, d60743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1488 q = 1) (hb : d52832 q = 1) : d60744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d52832, d60744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1488, d52832, d60744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4506 q = 1) (hb : d52833 q = 1) : d60745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d52833, d60745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4506, d52833, d60745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4507 q = 1) (hb : d52854 q = 1) : d60746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d52854, d60746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d52854, d60746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4508 q = 1) (hb : d52855 q = 1) : d60747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d52855, d60747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d52855, d60747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4509 q = 1) (hb : d52856 q = 1) : d60748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d52856, d60748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d52856, d60748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1377 (p : Pattern) (ha : d52862 p = 1) (hb : d60483 p = 1) : d60765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4510 q = 1) (hb : d52857 q = 1) : d60749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d52857, d60749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4510, d52857, d60749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1376 q ha hb
  have h3 (q : Pattern) (ha : d1504 q = 1) (hb : d52859 q = 1) : d60760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52859, d60760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1504, d52859, d60760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1369 q ha hb
  have h4 (q : Pattern) (ha : d51750 q = 1) (hb : d52860 q = 1) : d60761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51750, d52860, d60761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51750, d52860, d60761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51751 q = 1) (hb : d52861 q = 1) : d60762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51751, d52861, d60762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51751, d52861, d60762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51752 q = 1) (hb : d52862 q = 1) : d60763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51752, d52862, d60763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51752, d52862, d60763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51753 q = 1) (hb : d52862 q = 1) : d60764 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51753, d60764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51753, d60764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52862 q = 1) (hb : d60483 q = 1) : d60765 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60483, d60765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60483, d60765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1378 (p : Pattern) (ha : d60380 p = 1) (hb : d60489 p = 1) : d60771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60375 q = 1) (hb : d60484 q = 1) : d60766 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60375, d60484, d60766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60375, d60484, d60766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1377 q ha hb
  have h2 (q : Pattern) (ha : d60376 q = 1) (hb : d60485 q = 1) : d60767 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60376, d60485, d60767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60376, d60485, d60767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60377 q = 1) (hb : d60486 q = 1) : d60768 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60377, d60486, d60768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60377, d60486, d60768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60378 q = 1) (hb : d60487 q = 1) : d60769 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60378, d60487, d60769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60378, d60487, d60769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60379 q = 1) (hb : d60488 q = 1) : d60770 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60379, d60488, d60770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60379, d60488, d60770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60380 q = 1) (hb : d60489 q = 1) : d60771 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60380, d60489, d60771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60380, d60489, d60771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1379 (p : Pattern) (ha : d1878 p = 1) (hb : d53030 p = 1) : d60783 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1863 q = 1) : d1863 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1864 q = 1) (hb : d53013 q = 1) : d18155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1865 q = 1) (hb : d53014 q = 1) : d18156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1869 q = 1) : d1869 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1870 q = 1) (hb : d53025 q = 1) : d18188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1871 q = 1) (hb : d53026 q = 1) : d18189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1872 q = 1) (hb : d53027 q = 1) : d60778 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d53027, d60778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1872, d53027, d60778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1877 q = 1) (hb : d53029 q = 1) : d18190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d53029, d18190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1877, d53029, d18190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1878 q = 1) (hb : d53030 q = 1) : d60783 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d53030, d60783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1878, d53030, d60783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1380 (p : Pattern) (ha : d1888 p = 1) (hb : d53043 p = 1) : d60791 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1869 q = 1) : d1869 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1870 q = 1) (hb : d53025 q = 1) : d18188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1871 q = 1) (hb : d53026 q = 1) : d18189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1877 q = 1) (hb : d53029 q = 1) : d18190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d53029, d18190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1877, d53029, d18190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1884 q = 1) : d1884 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d1597 q = 1) (hb : d53038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1598 q = 1) (hb : d53039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1885 q = 1) (hb : d53040 q = 1) : d60788 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d53040, d60788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1885, d53040, d60788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1886 q = 1) (hb : d53041 q = 1) : d60789 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d53041, d60789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1886, d53041, d60789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1887 q = 1) (hb : d53042 q = 1) : d60790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d53042, d60790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1887, d53042, d60790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1888 q = 1) (hb : d53043 q = 1) : d60791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1888, d53043, d60791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1888, d53043, d60791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1381 (p : Pattern) (ha : d1907 p = 1) (hb : d53054 p = 1) : d60810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d53044 q = 1) : d60792 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1379 q ha hb
    | true =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1380 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d53045 q = 1) : d60793 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d53046 q = 1) : d60794 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1897 q = 1) (hb : d53048 q = 1) : d60800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d53048, d60800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d53048, d60800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1906 q = 1) (hb : d53053 q = 1) : d60809 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d53053, d60809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1906, d53053, d60809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1907 q = 1) (hb : d53054 q = 1) : d60810 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d53054, d60810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1907, d53054, d60810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1382 (p : Pattern) (ha : d1974 p = 1) (hb : d53074 p = 1) : d60829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d53055 q = 1) : d60811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53055, d60811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1381 q ha hb
    | true =>
      simp only [d1908, d53055, d60811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d53056 q = 1) : d60812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53056, d60812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53056, d60812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d53061 q = 1) : d60826 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d53061, d60826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d53061, d60826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d53062 q = 1) : d60827 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d53062, d60827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d53062, d60827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d53063 q = 1) : d60828 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d53063, d60828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d53063, d60828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d53074 q = 1) : d60829 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d53074, d60829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d53074, d60829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1383 (p : Pattern) (ha : d1980 p = 1) (hb : d53173 p = 1) : d60835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d53159 q = 1) : d60830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d53159, d60830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1382 q ha hb
    | true =>
      simp only [d1975, d53159, d60830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d53160 q = 1) : d60831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d53160, d60831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d53160, d60831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d53161 q = 1) : d60832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d53161, d60832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d53161, d60832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d53162 q = 1) : d60833 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d53162, d60833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d53162, d60833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d53163 q = 1) : d60834 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d53163, d60834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d53163, d60834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d53173 q = 1) : d60835 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d53173, d60835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d53173, d60835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1384 (p : Pattern) (ha : d1867 p = 1) (hb : d53111 p = 1) : d60777 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1854 q = 1) : d1854 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1855 q = 1) (hb : d53108 q = 1) : d18123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53108, d18123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1855, d53108, d18123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1856 q = 1) (hb : d53109 q = 1) : d18124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d53109, d18124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1856, d53109, d18124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1858 q = 1) : d1858 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1859 q = 1) (hb : d52998 q = 1) : d18134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d52998, d18134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1859, d52998, d18134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1860 q = 1) (hb : d52999 q = 1) : d18135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d52999, d18135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1860, d52999, d18135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1861 q = 1) (hb : d53110 q = 1) : d60775 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d53110, d60775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1861, d53110, d60775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1863 q = 1) : d1863 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1864 q = 1) (hb : d53013 q = 1) : d18155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1865 q = 1) (hb : d53014 q = 1) : d18156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1866 q = 1) (hb : d53015 q = 1) : d60776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d53015, d60776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1866, d53015, d60776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1867 q = 1) (hb : d53111 q = 1) : d60777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d53111, d60777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1867, d53111, d60777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1385 (p : Pattern) (ha : d1873 p = 1) (hb : d53028 p = 1) : d60779 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1858 q = 1) : d1858 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1859 q = 1) (hb : d52998 q = 1) : d18134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d52998, d18134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1859, d52998, d18134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1860 q = 1) (hb : d52999 q = 1) : d18135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d52999, d18135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1860, d52999, d18135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1863 q = 1) : d1863 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1864 q = 1) (hb : d53013 q = 1) : d18155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1864, d53013, d18155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1865 q = 1) (hb : d53014 q = 1) : d18156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1865, d53014, d18156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1866 q = 1) (hb : d53015 q = 1) : d60776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d53015, d60776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1866, d53015, d60776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1869 q = 1) : d1869 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1870 q = 1) (hb : d53025 q = 1) : d18188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1870, d53025, d18188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1871 q = 1) (hb : d53026 q = 1) : d18189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1871, d53026, d18189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1872 q = 1) (hb : d53027 q = 1) : d60778 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d53027, d60778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1872, d53027, d60778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1873 q = 1) (hb : d53028 q = 1) : d60779 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d53028, d60779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1873, d53028, d60779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1386 (p : Pattern) (ha : d1894 p = 1) (hb : d53117 p = 1) : d60797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d53112 q = 1) : d60780 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53112, d60780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1384 q ha hb
    | true =>
      simp only [d1874, d53112, d60780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1385 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d53113 q = 1) : d60781 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53113, d60781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d53113, d60781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d53114 q = 1) : d60782 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53114, d60782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d53114, d60782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1879 q = 1) (hb : d53031 q = 1) : d60784 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53031, d60784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1385 q ha hb
    | true =>
      simp only [d1879, d53031, d60784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1379 q ha hb
  have h5 (q : Pattern) (ha : d1880 q = 1) (hb : d53032 q = 1) : d60785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53032, d60785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53032, d60785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1881 q = 1) (hb : d53033 q = 1) : d60786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53033, d60786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53033, d60786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1882 q = 1) (hb : d53115 q = 1) : d60787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d53115, d60787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1882, d53115, d60787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1889 q = 1) (hb : d53044 q = 1) : d60792 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1379 q ha hb
    | true =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1380 q ha hb
  have h9 (q : Pattern) (ha : d1890 q = 1) (hb : d53045 q = 1) : d60793 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1891 q = 1) (hb : d53046 q = 1) : d60794 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1892 q = 1) (hb : d53047 q = 1) : d60795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d53047, d60795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1892, d53047, d60795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1893 q = 1) (hb : d53116 q = 1) : d60796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d53116, d60796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1893, d53116, d60796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1894 q = 1) (hb : d53117 q = 1) : d60797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d53117, d60797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1894, d53117, d60797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1387 (p : Pattern) (ha : d1899 p = 1) (hb : d53050 p = 1) : d60802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53031 q = 1) : d60784 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53031, d60784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1385 q ha hb
    | true =>
      simp only [d1879, d53031, d60784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1379 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53032 q = 1) : d60785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53032, d60785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53032, d60785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53033 q = 1) : d60786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53033, d60786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53033, d60786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d53044 q = 1) : d60792 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1379 q ha hb
    | true =>
      simp only [d1889, d53044, d60792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1380 q ha hb
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d53045 q = 1) : d60793 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53045, d60793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d53046 q = 1) : d60794 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53046, d60794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1892 q = 1) (hb : d53047 q = 1) : d60795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d53047, d60795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d53047, d60795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1897 q = 1) (hb : d53048 q = 1) : d60800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d53048, d60800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1897, d53048, d60800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1898 q = 1) (hb : d53049 q = 1) : d60801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d53049, d60801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1898, d53049, d60801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1899 q = 1) (hb : d53050 q = 1) : d60802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d53050, d60802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1899, d53050, d60802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1388 (p : Pattern) (ha : d1905 p = 1) (hb : d53143 p = 1) : d60808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d53118 q = 1) : d60798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d53118, d60798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1386 q ha hb
    | true =>
      simp only [d1895, d53118, d60798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d53119 q = 1) : d60799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d53119, d60799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d53119, d60799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1900 q = 1) (hb : d53051 q = 1) : d60803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d53051, d60803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1387 q ha hb
    | true =>
      simp only [d1900, d53051, d60803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1901 q = 1) (hb : d53052 q = 1) : d60804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d53052, d60804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d53052, d60804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1902 q = 1) (hb : d53120 q = 1) : d60805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d53120, d60805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1902, d53120, d60805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1903 q = 1) (hb : d53121 q = 1) : d60806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d53121, d60806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1903, d53121, d60806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1904 q = 1) (hb : d53122 q = 1) : d60807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d53122, d60807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1904, d53122, d60807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1905 q = 1) (hb : d53143 q = 1) : d60808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d53143, d60808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1905, d53143, d60808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1389 (p : Pattern) (ha : d1913 p = 1) (hb : d53073 p = 1) : d60816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d53051 q = 1) : d60803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d53051, d60803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1387 q ha hb
    | true =>
      simp only [d1900, d53051, d60803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d53052 q = 1) : d60804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d53052, d60804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d53052, d60804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53055 q = 1) : d60811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53055, d60811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1381 q ha hb
    | true =>
      simp only [d1908, d53055, d60811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53056 q = 1) : d60812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53056, d60812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53056, d60812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d53057 q = 1) : d60813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d53057, d60813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d53057, d60813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d53058 q = 1) : d60814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d53058, d60814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, d53058, d60814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d53059 q = 1) : d60815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d53059, d60815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d53059, d60815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d53073 q = 1) : d60816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d53073, d60816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d53073, d60816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1390 (p : Pattern) (ha : d4549 p = 1) (hb : d53171 p = 1) : d60824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d53144 q = 1) : d60817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d53144, d60817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1388 q ha hb
    | true =>
      simp only [d1914, d53144, d60817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1389 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d53145 q = 1) : d60818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d53145, d60818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d53145, d60818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1964 q = 1) (hb : d53146 q = 1) : d60819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d53146, d60819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1389 q ha hb
    | true =>
      simp only [d1964, d53146, d60819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1965 q = 1) (hb : d53147 q = 1) : d60820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d53147, d60820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1965, d53147, d60820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4546 q = 1) (hb : d53148 q = 1) : d60821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d53148, d60821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4546, d53148, d60821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4547 q = 1) (hb : d53169 q = 1) : d60822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d53169, d60822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d53169, d60822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4548 q = 1) (hb : d53170 q = 1) : d60823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d53170, d60823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d53170, d60823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4549 q = 1) (hb : d53171 q = 1) : d60824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d53171, d60824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d53171, d60824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1391 (p : Pattern) (ha : d53177 p = 1) (hb : d60493 p = 1) : d60841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4550 q = 1) (hb : d53172 q = 1) : d60825 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d53172, d60825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4550, d53172, d60825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1390 q ha hb
  have h3 (q : Pattern) (ha : d1981 q = 1) (hb : d53174 q = 1) : d60836 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53174, d60836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1981, d53174, d60836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1383 q ha hb
  have h4 (q : Pattern) (ha : d51778 q = 1) (hb : d53175 q = 1) : d60837 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51778, d53175, d60837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51778, d53175, d60837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51779 q = 1) (hb : d53176 q = 1) : d60838 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51779, d53176, d60838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51779, d53176, d60838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51780 q = 1) (hb : d53177 q = 1) : d60839 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51780, d53177, d60839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51780, d53177, d60839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51781 q = 1) (hb : d53177 q = 1) : d60840 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51781, d60840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51781, d60840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53177 q = 1) (hb : d60493 q = 1) : d60841 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60493, d60841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60493, d60841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1392 (p : Pattern) (ha : d60389 p = 1) (hb : d60499 p = 1) : d60847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60384 q = 1) (hb : d60494 q = 1) : d60842 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60384, d60494, d60842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60384, d60494, d60842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1391 q ha hb
  have h2 (q : Pattern) (ha : d60385 q = 1) (hb : d60495 q = 1) : d60843 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60385, d60495, d60843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60385, d60495, d60843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60386 q = 1) (hb : d60496 q = 1) : d60844 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60386, d60496, d60844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60386, d60496, d60844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60387 q = 1) (hb : d60497 q = 1) : d60845 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60387, d60497, d60845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60387, d60497, d60845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60388 q = 1) (hb : d60498 q = 1) : d60846 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60388, d60498, d60846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60388, d60498, d60846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60389 q = 1) (hb : d60499 q = 1) : d60847 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60389, d60499, d60847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60389, d60499, d60847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1393 (p : Pattern) (ha : d2356 p = 1) (hb : d53351 p = 1) : d60860 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2341 q = 1) : d2341 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2342 q = 1) (hb : d53334 q = 1) : d18336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2343 q = 1) (hb : d53335 q = 1) : d18337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2347 q = 1) : d2347 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2348 q = 1) (hb : d53346 q = 1) : d18369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2349 q = 1) (hb : d53347 q = 1) : d18370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2350 q = 1) (hb : d53348 q = 1) : d60855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53348, d60855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2350, d53348, d60855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2355 q = 1) (hb : d53350 q = 1) : d18371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d53350, d18371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2355, d53350, d18371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2356 q = 1) (hb : d53351 q = 1) : d60860 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2356, d53351, d60860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2356, d53351, d60860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1394 (p : Pattern) (ha : d2366 p = 1) (hb : d53364 p = 1) : d60868 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2347 q = 1) : d2347 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2348 q = 1) (hb : d53346 q = 1) : d18369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2349 q = 1) (hb : d53347 q = 1) : d18370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2355 q = 1) (hb : d53350 q = 1) : d18371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d53350, d18371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2355, d53350, d18371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2362 q = 1) : d2362 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2363 q = 1) (hb : d53361 q = 1) : d60865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53361, d60865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2363, d53361, d60865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2364 q = 1) (hb : d53362 q = 1) : d60866 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53362, d60866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2364, d53362, d60866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2365 q = 1) (hb : d53363 q = 1) : d60867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53363, d60867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2365, d53363, d60867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2366 q = 1) (hb : d53364 q = 1) : d60868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2366, d53364, d60868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2366, d53364, d60868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro1395 (p : Pattern) (ha : d2385 p = 1) (hb : d53375 p = 1) : d60887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2367 q = 1) (hb : d53365 q = 1) : d60869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1393 q ha hb
    | true =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1394 q ha hb
  have h2 (q : Pattern) (ha : d2368 q = 1) (hb : d53366 q = 1) : d60870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2369 q = 1) (hb : d53367 q = 1) : d60871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2375 q = 1) (hb : d53369 q = 1) : d60877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d53369, d60877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2375, d53369, d60877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2384 q = 1) (hb : d53374 q = 1) : d60886 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d53374, d60886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2384, d53374, d60886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2385 q = 1) (hb : d53375 q = 1) : d60887 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d53375, d60887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2385, d53375, d60887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1396 (p : Pattern) (ha : d2452 p = 1) (hb : d53395 p = 1) : d60906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d53376 q = 1) : d60888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53376, d60888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1395 q ha hb
    | true =>
      simp only [d2386, d53376, d60888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d53377 q = 1) : d60889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53377, d60889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53377, d60889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d53382 q = 1) : d60903 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d53382, d60903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d53382, d60903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d53383 q = 1) : d60904 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d53383, d60904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d53383, d60904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d53384 q = 1) : d60905 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d53384, d60905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d53384, d60905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d53395 q = 1) : d60906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d53395, d60906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d53395, d60906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1397 (p : Pattern) (ha : d2458 p = 1) (hb : d53490 p = 1) : d60912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d53476 q = 1) : d60907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d53476, d60907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1396 q ha hb
    | true =>
      simp only [d2453, d53476, d60907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d53477 q = 1) : d60908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d53477, d60908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d53477, d60908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d53478 q = 1) : d60909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d53478, d60909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d53478, d60909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d53479 q = 1) : d60910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d53479, d60910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d53479, d60910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d53480 q = 1) : d60911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d53480, d60911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d53480, d60911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d53490 q = 1) : d60912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d53490, d60912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d53490, d60912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1398 (p : Pattern) (ha : d2345 p = 1) (hb : d53428 p = 1) : d60854 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2332 q = 1) : d2332 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2333 q = 1) (hb : d53425 q = 1) : d18309 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53425, d18309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2333, d53425, d18309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2334 q = 1) (hb : d53426 q = 1) : d18310 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d53426, d18310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2334, d53426, d18310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2336 q = 1) : d2336 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2337 q = 1) (hb : d53316 q = 1) : d18318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53316, d18318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2337, d53316, d18318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2338 q = 1) (hb : d53317 q = 1) : d18319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53317, d18319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2338, d53317, d18319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2339 q = 1) (hb : d53427 q = 1) : d60852 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, d53427, d60852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2339, d53427, d60852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2341 q = 1) : d2341 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d2342 q = 1) (hb : d53334 q = 1) : d18336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2343 q = 1) (hb : d53335 q = 1) : d18337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d2344 q = 1) (hb : d53336 q = 1) : d60853 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d53336, d60853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2344, d53336, d60853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2345 q = 1) (hb : d53428 q = 1) : d60854 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2345, d53428, d60854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2345, d53428, d60854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1399 (p : Pattern) (ha : d2351 p = 1) (hb : d53349 p = 1) : d60856 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2336 q = 1) : d2336 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2337 q = 1) (hb : d53316 q = 1) : d18318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53316, d18318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2337, d53316, d18318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2338 q = 1) (hb : d53317 q = 1) : d18319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53317, d18319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2338, d53317, d18319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2341 q = 1) : d2341 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2342 q = 1) (hb : d53334 q = 1) : d18336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2342, d53334, d18336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2343 q = 1) (hb : d53335 q = 1) : d18337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2343, d53335, d18337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2344 q = 1) (hb : d53336 q = 1) : d60853 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d53336, d60853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2344, d53336, d60853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2347 q = 1) : d2347 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d2348 q = 1) (hb : d53346 q = 1) : d18369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2348, d53346, d18369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2349 q = 1) (hb : d53347 q = 1) : d18370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2349, d53347, d18370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d2350 q = 1) (hb : d53348 q = 1) : d60855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53348, d60855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2350, d53348, d60855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2351 q = 1) (hb : d53349 q = 1) : d60856 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2351, d53349, d60856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2351, d53349, d60856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro1400 (p : Pattern) (ha : d2372 p = 1) (hb : d53434 p = 1) : d60874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d53429 q = 1) : d60857 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53429, d60857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1398 q ha hb
    | true =>
      simp only [d2352, d53429, d60857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1399 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d53430 q = 1) : d60858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53430, d60858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d53430, d60858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d53431 q = 1) : d60859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53431, d60859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d53431, d60859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2357 q = 1) (hb : d53352 q = 1) : d60861 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53352, d60861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1399 q ha hb
    | true =>
      simp only [d2357, d53352, d60861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1393 q ha hb
  have h5 (q : Pattern) (ha : d2358 q = 1) (hb : d53353 q = 1) : d60862 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53353, d60862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53353, d60862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2359 q = 1) (hb : d53354 q = 1) : d60863 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53354, d60863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53354, d60863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2360 q = 1) (hb : d53432 q = 1) : d60864 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d53432, d60864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2360, d53432, d60864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2367 q = 1) (hb : d53365 q = 1) : d60869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1393 q ha hb
    | true =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1394 q ha hb
  have h9 (q : Pattern) (ha : d2368 q = 1) (hb : d53366 q = 1) : d60870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2369 q = 1) (hb : d53367 q = 1) : d60871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2370 q = 1) (hb : d53368 q = 1) : d60872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d53368, d60872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2370, d53368, d60872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2371 q = 1) (hb : d53433 q = 1) : d60873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d53433, d60873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2371, d53433, d60873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2372 q = 1) (hb : d53434 q = 1) : d60874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d53434, d60874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2372, d53434, d60874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro1401 (p : Pattern) (ha : d2377 p = 1) (hb : d53371 p = 1) : d60879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53352 q = 1) : d60861 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53352, d60861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1399 q ha hb
    | true =>
      simp only [d2357, d53352, d60861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1393 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53353 q = 1) : d60862 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53353, d60862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53353, d60862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53354 q = 1) : d60863 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53354, d60863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53354, d60863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2367 q = 1) (hb : d53365 q = 1) : d60869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1393 q ha hb
    | true =>
      simp only [d2367, d53365, d60869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1394 q ha hb
  have h5 (q : Pattern) (ha : d2368 q = 1) (hb : d53366 q = 1) : d60870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53366, d60870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2369 q = 1) (hb : d53367 q = 1) : d60871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53367, d60871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2370 q = 1) (hb : d53368 q = 1) : d60872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d53368, d60872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2370, d53368, d60872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2375 q = 1) (hb : d53369 q = 1) : d60877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d53369, d60877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2375, d53369, d60877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2376 q = 1) (hb : d53370 q = 1) : d60878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d53370, d60878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2376, d53370, d60878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2377 q = 1) (hb : d53371 q = 1) : d60879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d53371, d60879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2377, d53371, d60879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro1402 (p : Pattern) (ha : d2383 p = 1) (hb : d53460 p = 1) : d60885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d53435 q = 1) : d60875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d53435, d60875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1400 q ha hb
    | true =>
      simp only [d2373, d53435, d60875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d53436 q = 1) : d60876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d53436, d60876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d53436, d60876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2378 q = 1) (hb : d53372 q = 1) : d60880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d53372, d60880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1401 q ha hb
    | true =>
      simp only [d2378, d53372, d60880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2379 q = 1) (hb : d53373 q = 1) : d60881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d53373, d60881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d53373, d60881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2380 q = 1) (hb : d53437 q = 1) : d60882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2380, d53437, d60882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2380, d53437, d60882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2381 q = 1) (hb : d53438 q = 1) : d60883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2381, d53438, d60883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2381, d53438, d60883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2382 q = 1) (hb : d53439 q = 1) : d60884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2382, d53439, d60884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2382, d53439, d60884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2383 q = 1) (hb : d53460 q = 1) : d60885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2383, d53460, d60885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2383, d53460, d60885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1403 (p : Pattern) (ha : d2391 p = 1) (hb : d53394 p = 1) : d60893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d53372 q = 1) : d60880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d53372, d60880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1401 q ha hb
    | true =>
      simp only [d2378, d53372, d60880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d53373 q = 1) : d60881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d53373, d60881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d53373, d60881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53376 q = 1) : d60888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53376, d60888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1395 q ha hb
    | true =>
      simp only [d2386, d53376, d60888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53377 q = 1) : d60889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53377, d60889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53377, d60889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2388 q = 1) (hb : d53378 q = 1) : d60890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d53378, d60890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, d53378, d60890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2389 q = 1) (hb : d53379 q = 1) : d60891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d53379, d60891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2389, d53379, d60891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2390 q = 1) (hb : d53380 q = 1) : d60892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d53380, d60892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2390, d53380, d60892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2391 q = 1) (hb : d53394 q = 1) : d60893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d53394, d60893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2391, d53394, d60893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro1404 (p : Pattern) (ha : d4590 p = 1) (hb : d53488 p = 1) : d60901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2392 q = 1) (hb : d53461 q = 1) : d60894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d53461, d60894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1402 q ha hb
    | true =>
      simp only [d2392, d53461, d60894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1403 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d53462 q = 1) : d60895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d53462, d60895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4586, d53462, d60895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2442 q = 1) (hb : d53463 q = 1) : d60896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d53463, d60896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1403 q ha hb
    | true =>
      simp only [d2442, d53463, d60896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2443 q = 1) (hb : d53464 q = 1) : d60897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d53464, d60897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2443, d53464, d60897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4587 q = 1) (hb : d53465 q = 1) : d60898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d53465, d60898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4587, d53465, d60898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4588 q = 1) (hb : d53486 q = 1) : d60899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d53486, d60899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d53486, d60899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4589 q = 1) (hb : d53487 q = 1) : d60900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d53487, d60900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d53487, d60900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4590 q = 1) (hb : d53488 q = 1) : d60901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d53488, d60901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d53488, d60901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro1405 (p : Pattern) (ha : d53494 p = 1) (hb : d60504 p = 1) : d60918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4591 q = 1) (hb : d53489 q = 1) : d60902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d53489, d60902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4591, d53489, d60902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1404 q ha hb
  have h3 (q : Pattern) (ha : d2459 q = 1) (hb : d53491 q = 1) : d60913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53491, d60913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2459, d53491, d60913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1397 q ha hb
  have h4 (q : Pattern) (ha : d51807 q = 1) (hb : d53492 q = 1) : d60914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51807, d53492, d60914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51807, d53492, d60914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51808 q = 1) (hb : d53493 q = 1) : d60915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51808, d53493, d60915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51808, d53493, d60915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51809 q = 1) (hb : d53494 q = 1) : d60916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51809, d53494, d60916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51809, d53494, d60916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51810 q = 1) (hb : d53494 q = 1) : d60917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51810, d60917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51810, d60917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53494 q = 1) (hb : d60504 q = 1) : d60918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60504, d60918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60504, d60918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro1406 (p : Pattern) (ha : d60399 p = 1) (hb : d60510 p = 1) : d60924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60394 q = 1) (hb : d60505 q = 1) : d60919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60394, d60505, d60919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60394, d60505, d60919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1405 q ha hb
  have h2 (q : Pattern) (ha : d60395 q = 1) (hb : d60506 q = 1) : d60920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60395, d60506, d60920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60395, d60506, d60920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60396 q = 1) (hb : d60507 q = 1) : d60921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60396, d60507, d60921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60396, d60507, d60921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60397 q = 1) (hb : d60508 q = 1) : d60922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60397, d60508, d60922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60397, d60508, d60922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60398 q = 1) (hb : d60509 q = 1) : d60923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60398, d60509, d60923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60398, d60509, d60923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60399 q = 1) (hb : d60510 q = 1) : d60924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60399, d60510, d60924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60399, d60510, d60924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1407 (p : Pattern) (ha : d60405 p = 1) (hb : d60516 p = 1) : d60930 p = 1 := by
  have h0 (q : Pattern) (ha : d60366 q = 1) (hb : d60473 q = 1) : d60650 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60366, d60473, d60650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1339 q ha hb
    | true =>
      simp only [d60366, d60473, d60650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1350 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60373 q = 1) (hb : d60481 q = 1) : d60698 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60373, d60481, d60698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60373, d60481, d60698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1364 q ha hb
  have h3 (q : Pattern) (ha : d60374 q = 1) (hb : d60482 q = 1) : d60699 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60374, d60482, d60699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60374, d60482, d60699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60381 q = 1) (hb : d60490 q = 1) : d60772 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60381, d60490, d60772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60381, d60490, d60772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1378 q ha hb
  have h5 (q : Pattern) (ha : d60382 q = 1) (hb : d60491 q = 1) : d60773 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60382, d60491, d60773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60382, d60491, d60773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60383 q = 1) (hb : d60492 q = 1) : d60774 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60383, d60492, d60774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60383, d60492, d60774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60390 q = 1) (hb : d60500 q = 1) : d60848 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60390, d60500, d60848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60390, d60500, d60848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1392 q ha hb
  have h8 (q : Pattern) (ha : d60391 q = 1) (hb : d60501 q = 1) : d60849 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60391, d60501, d60849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60391, d60501, d60849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60392 q = 1) (hb : d60502 q = 1) : d60850 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60392, d60502, d60850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60392, d60502, d60850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d60393 q = 1) (hb : d60503 q = 1) : d60851 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60393, d60503, d60851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d60393, d60503, d60851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d60400 q = 1) (hb : d60511 q = 1) : d60925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60400, d60511, d60925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60400, d60511, d60925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1406 q ha hb
  have h12 (q : Pattern) (ha : d60401 q = 1) (hb : d60512 q = 1) : d60926 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60401, d60512, d60926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60401, d60512, d60926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d60402 q = 1) (hb : d60513 q = 1) : d60927 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60402, d60513, d60927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60402, d60513, d60927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d60403 q = 1) (hb : d60514 q = 1) : d60928 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60403, d60514, d60928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60403, d60514, d60928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d60404 q = 1) (hb : d60515 q = 1) : d60929 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d60404, d60515, d60929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d60404, d60515, d60929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d60405 q = 1) (hb : d60516 q = 1) : d60930 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d60405, d60516, d60930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d60405, d60516, d60930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1408 (p : Pattern) (ha : d60411 p = 1) (hb : d60522 p = 1) : d60936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60406 q = 1) (hb : d60517 q = 1) : d60931 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d60406, d60517, d60931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1407 q ha hb
    | true =>
      simp only [d60406, d60517, d60931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60407 q = 1) (hb : d60518 q = 1) : d60932 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d60407, d60518, d60932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60407, d60518, d60932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60408 q = 1) (hb : d60519 q = 1) : d60933 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d60408, d60519, d60933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60408, d60519, d60933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60409 q = 1) (hb : d60520 q = 1) : d60934 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d60409, d60520, d60934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60409, d60520, d60934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60410 q = 1) (hb : d60521 q = 1) : d60935 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d60410, d60521, d60935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60410, d60521, d60935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60411 q = 1) (hb : d60522 q = 1) : d60936 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d60411, d60522, d60936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60411, d60522, d60936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1409 (p : Pattern) (ha : d60417 p = 1) (hb : d60528 p = 1) : d60942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60412 q = 1) (hb : d60523 q = 1) : d60937 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d60412, d60523, d60937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1408 q ha hb
    | true =>
      simp only [d60412, d60523, d60937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60413 q = 1) (hb : d60524 q = 1) : d60938 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d60413, d60524, d60938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60413, d60524, d60938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60414 q = 1) (hb : d60525 q = 1) : d60939 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d60414, d60525, d60939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60414, d60525, d60939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60415 q = 1) (hb : d60526 q = 1) : d60940 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d60415, d60526, d60940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60415, d60526, d60940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60416 q = 1) (hb : d60527 q = 1) : d60941 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d60416, d60527, d60941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60416, d60527, d60941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60417 q = 1) (hb : d60528 q = 1) : d60942 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d60417, d60528, d60942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60417, d60528, d60942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1410 (p : Pattern) (ha : d60423 p = 1) (hb : d60534 p = 1) : d60948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60418 q = 1) (hb : d60529 q = 1) : d60943 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d60418, d60529, d60943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1409 q ha hb
    | true =>
      simp only [d60418, d60529, d60943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60419 q = 1) (hb : d60530 q = 1) : d60944 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d60419, d60530, d60944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60419, d60530, d60944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60420 q = 1) (hb : d60531 q = 1) : d60945 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d60420, d60531, d60945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60420, d60531, d60945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60421 q = 1) (hb : d60532 q = 1) : d60946 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d60421, d60532, d60946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60421, d60532, d60946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60422 q = 1) (hb : d60533 q = 1) : d60947 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d60422, d60533, d60947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60422, d60533, d60947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60423 q = 1) (hb : d60534 q = 1) : d60948 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d60423, d60534, d60948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60423, d60534, d60948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1411 (p : Pattern) (ha : d60429 p = 1) (hb : d60540 p = 1) : d60954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60424 q = 1) (hb : d60535 q = 1) : d60949 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d60424, d60535, d60949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1410 q ha hb
    | true =>
      simp only [d60424, d60535, d60949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60425 q = 1) (hb : d60536 q = 1) : d60950 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d60425, d60536, d60950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60425, d60536, d60950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60426 q = 1) (hb : d60537 q = 1) : d60951 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d60426, d60537, d60951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60426, d60537, d60951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60427 q = 1) (hb : d60538 q = 1) : d60952 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d60427, d60538, d60952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60427, d60538, d60952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60428 q = 1) (hb : d60539 q = 1) : d60953 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d60428, d60539, d60953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60428, d60539, d60953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60429 q = 1) (hb : d60540 q = 1) : d60954 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d60429, d60540, d60954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60429, d60540, d60954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1412 (p : Pattern) (ha : d60435 p = 1) (hb : d60546 p = 1) : d60960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60430 q = 1) (hb : d60541 q = 1) : d60955 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d60430, d60541, d60955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1411 q ha hb
    | true =>
      simp only [d60430, d60541, d60955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60431 q = 1) (hb : d60542 q = 1) : d60956 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d60431, d60542, d60956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60431, d60542, d60956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60432 q = 1) (hb : d60543 q = 1) : d60957 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d60432, d60543, d60957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60432, d60543, d60957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60433 q = 1) (hb : d60544 q = 1) : d60958 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d60433, d60544, d60958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60433, d60544, d60958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60434 q = 1) (hb : d60545 q = 1) : d60959 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d60434, d60545, d60959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60434, d60545, d60959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60435 q = 1) (hb : d60546 q = 1) : d60960 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d60435, d60546, d60960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60435, d60546, d60960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1413 (p : Pattern) (ha : d60441 p = 1) (hb : d60552 p = 1) : d60966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60436 q = 1) (hb : d60547 q = 1) : d60961 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d60436, d60547, d60961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1412 q ha hb
    | true =>
      simp only [d60436, d60547, d60961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60437 q = 1) (hb : d60548 q = 1) : d60962 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d60437, d60548, d60962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60437, d60548, d60962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60438 q = 1) (hb : d60549 q = 1) : d60963 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d60438, d60549, d60963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60438, d60549, d60963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60439 q = 1) (hb : d60550 q = 1) : d60964 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d60439, d60550, d60964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60439, d60550, d60964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60440 q = 1) (hb : d60551 q = 1) : d60965 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d60440, d60551, d60965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60440, d60551, d60965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60441 q = 1) (hb : d60552 q = 1) : d60966 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d60441, d60552, d60966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60441, d60552, d60966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1414 (p : Pattern) (ha : d60447 p = 1) (hb : d60558 p = 1) : d60972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60442 q = 1) (hb : d60553 q = 1) : d60967 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d60442, d60553, d60967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1413 q ha hb
    | true =>
      simp only [d60442, d60553, d60967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60443 q = 1) (hb : d60554 q = 1) : d60968 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d60443, d60554, d60968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60443, d60554, d60968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60444 q = 1) (hb : d60555 q = 1) : d60969 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d60444, d60555, d60969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60444, d60555, d60969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60445 q = 1) (hb : d60556 q = 1) : d60970 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d60445, d60556, d60970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60445, d60556, d60970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60446 q = 1) (hb : d60557 q = 1) : d60971 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d60446, d60557, d60971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60446, d60557, d60971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60447 q = 1) (hb : d60558 q = 1) : d60972 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d60447, d60558, d60972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60447, d60558, d60972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1415 (p : Pattern) (ha : d53647 p = 1) (hb : d60240 p = 1) : d60973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53646 q = 1) (hb : d54517 q = 1) : d53646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53647 q = 1) (hb : d60240 q = 1) : d60973 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d60240, d60973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53647, d60240, d60973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1416 (p : Pattern) (ha : d53671 p = 1) (hb : d60240 p = 1) : d60979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53660 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53670 q = 1) (hb : d54517 q = 1) : d53670 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53671 q = 1) (hb : d60240 q = 1) : d60979 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d60240, d60979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53671, d60240, d60979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1417 (p : Pattern) (ha : d53677 p = 1) (hb : d60240 p = 1) : d60985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d60240 q = 1) : d60974 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d60974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d60974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1415 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d60240 q = 1) : d60975 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d60975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d60975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d60240 q = 1) : d60976 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d60976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d60976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d60240 q = 1) : d60977 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d60977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d60977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d60240 q = 1) : d60978 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d60978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d60978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d60240 q = 1) : d60980 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d60980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d60980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1416 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d60240 q = 1) : d60981 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d60981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d60981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d60240 q = 1) : d60982 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d60982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d60982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d60240 q = 1) : d60983 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d60983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d60983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d60240 q = 1) : d60984 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d60984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d60984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d60240 q = 1) : d60985 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d60985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d60985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro1418 (p : Pattern) (ha : d53697 p = 1) (hb : d60240 p = 1) : d60986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53685 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53696 q = 1) (hb : d54517 q = 1) : d53696 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53697 q = 1) (hb : d60240 q = 1) : d60986 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d60240, d60986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53697, d60240, d60986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1419 (p : Pattern) (ha : d53703 p = 1) (hb : d60240 p = 1) : d60992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d60240 q = 1) : d60987 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d60987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d60987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1418 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d60240 q = 1) : d60988 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d60988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d60988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d60240 q = 1) : d60989 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d60989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d60989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d60240 q = 1) : d60990 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d60990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d60990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d60240 q = 1) : d60991 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d60991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d60991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d60240 q = 1) : d60992 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d60992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d60992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1420 (p : Pattern) (ha : d53724 p = 1) (hb : d60240 p = 1) : d60994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53723 q = 1) (hb : d54517 q = 1) : d53723 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53724 q = 1) (hb : d60240 q = 1) : d60994 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d60240, d60994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53724, d60240, d60994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1421 (p : Pattern) (ha : d53730 p = 1) (hb : d60240 p = 1) : d61000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d60240 q = 1) : d60995 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d60995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d60995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1420 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d60240 q = 1) : d60996 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d60996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d60996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d60240 q = 1) : d60997 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d60997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d60997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d60240 q = 1) : d60998 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d60998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d60998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d60240 q = 1) : d60999 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d60999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d60999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d60240 q = 1) : d61000 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d61000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d61000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1422 (p : Pattern) (ha : d53752 p = 1) (hb : d60240 p = 1) : d61003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53751 q = 1) (hb : d54517 q = 1) : d53751 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53752 q = 1) (hb : d60240 q = 1) : d61003 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d60240, d61003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53752, d60240, d61003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1423 (p : Pattern) (ha : d53758 p = 1) (hb : d60240 p = 1) : d61009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d60240 q = 1) : d61004 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d61004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d61004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1422 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d60240 q = 1) : d61005 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d61005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d61005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d60240 q = 1) : d61006 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d61006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d61006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d60240 q = 1) : d61007 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d61007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d61007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d60240 q = 1) : d61008 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d61008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d61008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d60240 q = 1) : d61009 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d61009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d61009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1424 (p : Pattern) (ha : d53781 p = 1) (hb : d60240 p = 1) : d61013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53780 q = 1) (hb : d54517 q = 1) : d53780 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53781 q = 1) (hb : d60240 q = 1) : d61013 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d60240, d61013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53781, d60240, d61013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1425 (p : Pattern) (ha : d53787 p = 1) (hb : d60240 p = 1) : d61019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d60240 q = 1) : d61014 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d61014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d61014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1424 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d60240 q = 1) : d61015 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d61015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d61015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d60240 q = 1) : d61016 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d61016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d61016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d60240 q = 1) : d61017 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d61017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d61017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d60240 q = 1) : d61018 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d61018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d61018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d60240 q = 1) : d61019 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d61019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d61019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1426 (p : Pattern) (ha : d53811 p = 1) (hb : d60240 p = 1) : d61024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53799 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53810 q = 1) (hb : d54517 q = 1) : d53810 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53811 q = 1) (hb : d60240 q = 1) : d61024 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d60240, d61024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53811, d60240, d61024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro1427 (p : Pattern) (ha : d53817 p = 1) (hb : d60240 p = 1) : d61030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d60240 q = 1) : d61025 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d61025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d61025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1426 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d60240 q = 1) : d61026 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d61026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d61026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d60240 q = 1) : d61027 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d61027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d61027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d60240 q = 1) : d61028 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d61028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d61028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d60240 q = 1) : d61029 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d61029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d61029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d60240 q = 1) : d61030 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d61030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d61030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1428 (p : Pattern) (ha : d53823 p = 1) (hb : d60240 p = 1) : d61036 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d60240 q = 1) : d60993 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d60993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1417 q ha hb
    | true =>
      simp only [d53704, d60993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1419 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d60240 q = 1) : d61001 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d61001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d61001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1421 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d60240 q = 1) : d61002 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d61002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d61002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d60240 q = 1) : d61010 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d61010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d61010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1423 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d60240 q = 1) : d61011 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d61011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d61011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d60240 q = 1) : d61012 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d61012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d61012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d60240 q = 1) : d61020 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d61020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d61020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1425 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d60240 q = 1) : d61021 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d61021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d61021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d60240 q = 1) : d61022 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d61022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d61022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d60240 q = 1) : d61023 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d61023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d61023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d60240 q = 1) : d61031 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d61031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d61031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1427 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d60240 q = 1) : d61032 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d61032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d61032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d60240 q = 1) : d61033 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d61033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d61033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d60240 q = 1) : d61034 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d61034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d61034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d60240 q = 1) : d61035 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d61035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d61035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d60240 q = 1) : d61036 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d61036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d61036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1429 (p : Pattern) (ha : d53829 p = 1) (hb : d60240 p = 1) : d61042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d60240 q = 1) : d61037 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d61037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1428 q ha hb
    | true =>
      simp only [d53824, d61037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d60240 q = 1) : d61038 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d61038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d61038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d60240 q = 1) : d61039 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d61039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d61039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d60240 q = 1) : d61040 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d61040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d61040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d60240 q = 1) : d61041 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d61041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d61041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d60240 q = 1) : d61042 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d61042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d61042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1430 (p : Pattern) (ha : d53835 p = 1) (hb : d60240 p = 1) : d61048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d60240 q = 1) : d61043 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d61043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1429 q ha hb
    | true =>
      simp only [d53830, d61043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d60240 q = 1) : d61044 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d61044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d61044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d60240 q = 1) : d61045 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d61045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d61045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d60240 q = 1) : d61046 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d61046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d61046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d60240 q = 1) : d61047 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d61047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d61047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d60240 q = 1) : d61048 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d61048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d61048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1431 (p : Pattern) (ha : d53841 p = 1) (hb : d60240 p = 1) : d61054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d60240 q = 1) : d61049 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d61049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1430 q ha hb
    | true =>
      simp only [d53836, d61049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d60240 q = 1) : d61050 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d61050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d61050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d60240 q = 1) : d61051 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d61051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d61051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d60240 q = 1) : d61052 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d61052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d61052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d60240 q = 1) : d61053 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d61053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d61053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d60240 q = 1) : d61054 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d61054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d61054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1432 (p : Pattern) (ha : d53847 p = 1) (hb : d60240 p = 1) : d61060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d60240 q = 1) : d61055 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d61055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1431 q ha hb
    | true =>
      simp only [d53842, d61055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d60240 q = 1) : d61056 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d61056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d61056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d60240 q = 1) : d61057 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d61057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d61057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d60240 q = 1) : d61058 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d61058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d61058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d60240 q = 1) : d61059 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d61059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d61059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d60240 q = 1) : d61060 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d61060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d61060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1433 (p : Pattern) (ha : d53853 p = 1) (hb : d60240 p = 1) : d61066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d60240 q = 1) : d61061 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d61061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1432 q ha hb
    | true =>
      simp only [d53848, d61061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d60240 q = 1) : d61062 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d61062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d61062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d60240 q = 1) : d61063 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d61063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d61063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d60240 q = 1) : d61064 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d61064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d61064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d60240 q = 1) : d61065 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d61065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d61065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d60240 q = 1) : d61066 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d61066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d61066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1434 (p : Pattern) (ha : d53859 p = 1) (hb : d60241 p = 1) : d61072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60240 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d60240 q = 1) : d61067 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d61067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1433 q ha hb
    | true =>
      simp only [d53854, d61067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d60240 q = 1) : d61068 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d61068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d61068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d60240 q = 1) : d61069 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d61069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d61069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d60240 q = 1) : d61070 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d61070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d61070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53858 q = 1) (hb : d60241 q = 1) : d61071 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d60241, d61071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d60241, d61071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d60241 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d60241 q = 1) : d61072 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d61072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53859, d61072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1435 (p : Pattern) (ha : d53865 p = 1) (hb : d60241 p = 1) : d61078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60241 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d60241 q = 1) : d61073 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d61073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1434 q ha hb
    | true =>
      simp only [d53860, d61073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d60241 q = 1) : d61074 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d61074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d61074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d60241 q = 1) : d61075 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d61075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d61075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d60241 q = 1) : d61076 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d61076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d61076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d60241 q = 1) : d61077 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d61077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d61077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d60241 q = 1) : d61078 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d61078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d61078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1436 (p : Pattern) (ha : d462 p = 1) (hb : d52038 p = 1) : d17696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51902 q = 1) : d17577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
    | true =>
      simp only [d84, d51902, d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d52025 q = 1) : d17692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d52025, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d52025, d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d52026 q = 1) : d17693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d52026, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d52026, d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d52036 q = 1) : d17694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d52036, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d52036, d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d52037 q = 1) : d17695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d52037, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d52037, d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d52038 q = 1) : d17696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d52038, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d52038, d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1437 (p : Pattern) (ha : d52042 p = 1) (hb : d60973 p = 1) : d61083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d463 q = 1) (hb : d52039 q = 1) : d17697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52039, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d463, d52039, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1436 q ha hb
  have h3 (q : Pattern) (ha : d52040 q = 1) (hb : d53643 q = 1) : d61079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d53643, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52040, d53643, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d52041 q = 1) (hb : d53644 q = 1) : d61080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d53644, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52041, d53644, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d52042 q = 1) (hb : d53645 q = 1) : d61081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d53645, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52042, d53645, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52042 q = 1) (hb : d53646 q = 1) : d61082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53646, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52042 q = 1) (hb : d60973 q = 1) : d61083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60973, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60973, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1438 (p : Pattern) (ha : d52170 p = 1) (hb : d53665 p = 1) : d61093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d52024 q = 1) : d17609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52024, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1330 q ha hb
    | true =>
      simp only [d244, d52024, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1325 q ha hb
  have h3 (q : Pattern) (ha : d52155 q = 1) (hb : d53661 q = 1) : d61089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d53661, d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52155, d53661, d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52158 q = 1) (hb : d53662 q = 1) : d61090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52158, d53662, d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52158, d53662, d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52168 q = 1) (hb : d53663 q = 1) : d61091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52168, d53663, d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52168, d53663, d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52169 q = 1) (hb : d53664 q = 1) : d61092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52169, d53664, d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52169, d53664, d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52170 q = 1) (hb : d53665 q = 1) : d61093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52170, d53665, d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52170, d53665, d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1439 (p : Pattern) (ha : d52176 p = 1) (hb : d60979 p = 1) : d61099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52171 q = 1) (hb : d53666 q = 1) : d61094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52171, d53666, d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52171, d53666, d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1438 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52174 q = 1) (hb : d53667 q = 1) : d61095 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52174, d53667, d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52174, d53667, d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52175 q = 1) (hb : d53668 q = 1) : d61096 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52175, d53668, d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52175, d53668, d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52176 q = 1) (hb : d53669 q = 1) : d61097 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52176, d53669, d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52176, d53669, d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52176 q = 1) (hb : d53670 q = 1) : d61098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53670, d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52176 q = 1) (hb : d60979 q = 1) : d61099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60979, d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60979, d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1440 (p : Pattern) (ha : d60359 p = 1) (hb : d60985 p = 1) : d61105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60349 q = 1) (hb : d60974 q = 1) : d61084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60349, d60974, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60349, d60974, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1437 q ha hb
  have h3 (q : Pattern) (ha : d60350 q = 1) (hb : d60975 q = 1) : d61085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60350, d60975, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60350, d60975, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60351 q = 1) (hb : d60976 q = 1) : d61086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60351, d60976, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60351, d60976, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60352 q = 1) (hb : d60977 q = 1) : d61087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60352, d60977, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60352, d60977, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60353 q = 1) (hb : d60978 q = 1) : d61088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60353, d60978, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60353, d60978, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60354 q = 1) (hb : d60980 q = 1) : d61100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60354, d60980, d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60354, d60980, d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1439 q ha hb
  have h8 (q : Pattern) (ha : d60355 q = 1) (hb : d60981 q = 1) : d61101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60355, d60981, d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60355, d60981, d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60356 q = 1) (hb : d60982 q = 1) : d61102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60356, d60982, d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60356, d60982, d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d60357 q = 1) (hb : d60983 q = 1) : d61103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60357, d60983, d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60357, d60983, d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d60358 q = 1) (hb : d60984 q = 1) : d61104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60358, d60984, d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60358, d60984, d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d60359 q = 1) (hb : d60985 q = 1) : d61105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60359, d60985, d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d60359, d60985, d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1441 (p : Pattern) (ha : d52355 p = 1) (hb : d53691 p = 1) : d61111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52249 q = 1) (hb : d53686 q = 1) : d61106 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52249, d53686, d61106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1347 q hb ha
    | true =>
      simp only [d52249, d53686, d61106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1341 q hb ha
  have h3 (q : Pattern) (ha : d52329 q = 1) (hb : d53687 q = 1) : d61107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d53687, d61107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52329, d53687, d61107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52332 q = 1) (hb : d53688 q = 1) : d61108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52332, d53688, d61108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52332, d53688, d61108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52353 q = 1) (hb : d53689 q = 1) : d61109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52353, d53689, d61109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52353, d53689, d61109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52354 q = 1) (hb : d53690 q = 1) : d61110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52354, d53690, d61110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52354, d53690, d61110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52355 q = 1) (hb : d53691 q = 1) : d61111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52355, d53691, d61111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52355, d53691, d61111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1442 (p : Pattern) (ha : d52361 p = 1) (hb : d60986 p = 1) : d61117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52356 q = 1) (hb : d53692 q = 1) : d61112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52356, d53692, d61112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52356, d53692, d61112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1441 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52359 q = 1) (hb : d53693 q = 1) : d61113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52359, d53693, d61113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52359, d53693, d61113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52360 q = 1) (hb : d53694 q = 1) : d61114 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52360, d53694, d61114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52360, d53694, d61114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52361 q = 1) (hb : d53695 q = 1) : d61115 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52361, d53695, d61115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52361, d53695, d61115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52361 q = 1) (hb : d53696 q = 1) : d61116 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d61116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53696, d61116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52361 q = 1) (hb : d60986 q = 1) : d61117 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60986, d61117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60986, d61117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1443 (p : Pattern) (ha : d60365 p = 1) (hb : d60992 p = 1) : d61123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60360 q = 1) (hb : d60987 q = 1) : d61118 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60360, d60987, d61118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60360, d60987, d61118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1442 q ha hb
  have h2 (q : Pattern) (ha : d60361 q = 1) (hb : d60988 q = 1) : d61119 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60361, d60988, d61119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60361, d60988, d61119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60362 q = 1) (hb : d60989 q = 1) : d61120 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60362, d60989, d61120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60362, d60989, d61120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60363 q = 1) (hb : d60990 q = 1) : d61121 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60363, d60990, d61121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60363, d60990, d61121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60364 q = 1) (hb : d60991 q = 1) : d61122 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60364, d60991, d61122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60364, d60991, d61122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60365 q = 1) (hb : d60992 q = 1) : d61123 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60365, d60992, d61123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60365, d60992, d61123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1444 (p : Pattern) (ha : d52576 p = 1) (hb : d53718 p = 1) : d61130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52471 q = 1) (hb : d53713 q = 1) : d61125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52471, d53713, d61125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1361 q hb ha
    | true =>
      simp only [d52471, d53713, d61125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1354 q hb ha
  have h3 (q : Pattern) (ha : d52550 q = 1) (hb : d53714 q = 1) : d61126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d53714, d61126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52550, d53714, d61126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52553 q = 1) (hb : d53715 q = 1) : d61127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52553, d53715, d61127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52553, d53715, d61127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52574 q = 1) (hb : d53716 q = 1) : d61128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52574, d53716, d61128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52574, d53716, d61128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52575 q = 1) (hb : d53717 q = 1) : d61129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52575, d53717, d61129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52575, d53717, d61129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52576 q = 1) (hb : d53718 q = 1) : d61130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52576, d53718, d61130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52576, d53718, d61130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1445 (p : Pattern) (ha : d52582 p = 1) (hb : d60994 p = 1) : d61136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52577 q = 1) (hb : d53719 q = 1) : d61131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52577, d53719, d61131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52577, d53719, d61131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1444 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52580 q = 1) (hb : d53720 q = 1) : d61132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52580, d53720, d61132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52580, d53720, d61132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52581 q = 1) (hb : d53721 q = 1) : d61133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52581, d53721, d61133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52581, d53721, d61133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52582 q = 1) (hb : d53722 q = 1) : d61134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52582, d53722, d61134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52582, d53722, d61134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52582 q = 1) (hb : d53723 q = 1) : d61135 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d61135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53723, d61135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52582 q = 1) (hb : d60994 q = 1) : d61136 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60994, d61136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60994, d61136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1446 (p : Pattern) (ha : d60372 p = 1) (hb : d61000 p = 1) : d61142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60367 q = 1) (hb : d60995 q = 1) : d61137 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60367, d60995, d61137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60367, d60995, d61137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1445 q ha hb
  have h2 (q : Pattern) (ha : d60368 q = 1) (hb : d60996 q = 1) : d61138 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60368, d60996, d61138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60368, d60996, d61138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60369 q = 1) (hb : d60997 q = 1) : d61139 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60369, d60997, d61139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60369, d60997, d61139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60370 q = 1) (hb : d60998 q = 1) : d61140 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60370, d60998, d61140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60370, d60998, d61140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60371 q = 1) (hb : d60999 q = 1) : d61141 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60371, d60999, d61141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60371, d60999, d61141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60372 q = 1) (hb : d61000 q = 1) : d61142 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60372, d61000, d61142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60372, d61000, d61142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1447 (p : Pattern) (ha : d52856 p = 1) (hb : d53746 p = 1) : d61150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52754 q = 1) (hb : d53741 q = 1) : d61145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52754, d53741, d61145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1375 q hb ha
    | true =>
      simp only [d52754, d53741, d61145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1368 q hb ha
  have h3 (q : Pattern) (ha : d52830 q = 1) (hb : d53742 q = 1) : d61146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d53742, d61146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52830, d53742, d61146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52833 q = 1) (hb : d53743 q = 1) : d61147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52833, d53743, d61147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52833, d53743, d61147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52854 q = 1) (hb : d53744 q = 1) : d61148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52854, d53744, d61148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52854, d53744, d61148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52855 q = 1) (hb : d53745 q = 1) : d61149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52855, d53745, d61149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52855, d53745, d61149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52856 q = 1) (hb : d53746 q = 1) : d61150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52856, d53746, d61150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52856, d53746, d61150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1448 (p : Pattern) (ha : d52862 p = 1) (hb : d61003 p = 1) : d61156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52857 q = 1) (hb : d53747 q = 1) : d61151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52857, d53747, d61151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52857, d53747, d61151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1447 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52860 q = 1) (hb : d53748 q = 1) : d61152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52860, d53748, d61152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52860, d53748, d61152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d52861 q = 1) (hb : d53749 q = 1) : d61153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52861, d53749, d61153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52861, d53749, d61153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d52862 q = 1) (hb : d53750 q = 1) : d61154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52862, d53750, d61154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52862, d53750, d61154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d52862 q = 1) (hb : d53751 q = 1) : d61155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d61155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53751, d61155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52862 q = 1) (hb : d61003 q = 1) : d61156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61003, d61156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61003, d61156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1449 (p : Pattern) (ha : d60380 p = 1) (hb : d61009 p = 1) : d61162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60375 q = 1) (hb : d61004 q = 1) : d61157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60375, d61004, d61157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60375, d61004, d61157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1448 q ha hb
  have h2 (q : Pattern) (ha : d60376 q = 1) (hb : d61005 q = 1) : d61158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60376, d61005, d61158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60376, d61005, d61158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60377 q = 1) (hb : d61006 q = 1) : d61159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60377, d61006, d61159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60377, d61006, d61159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60378 q = 1) (hb : d61007 q = 1) : d61160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60378, d61007, d61160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60378, d61007, d61160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60379 q = 1) (hb : d61008 q = 1) : d61161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60379, d61008, d61161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60379, d61008, d61161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60380 q = 1) (hb : d61009 q = 1) : d61162 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60380, d61009, d61162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60380, d61009, d61162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1450 (p : Pattern) (ha : d53171 p = 1) (hb : d53775 p = 1) : d61171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53075 q = 1) (hb : d53770 q = 1) : d61166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53075, d53770, d61166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1389 q hb ha
    | true =>
      simp only [d53075, d53770, d61166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1382 q hb ha
  have h3 (q : Pattern) (ha : d53145 q = 1) (hb : d53771 q = 1) : d61167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d53771, d61167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53145, d53771, d61167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53148 q = 1) (hb : d53772 q = 1) : d61168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53148, d53772, d61168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53148, d53772, d61168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53169 q = 1) (hb : d53773 q = 1) : d61169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53169, d53773, d61169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53169, d53773, d61169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53170 q = 1) (hb : d53774 q = 1) : d61170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53170, d53774, d61170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53170, d53774, d61170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53171 q = 1) (hb : d53775 q = 1) : d61171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53171, d53775, d61171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53171, d53775, d61171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1451 (p : Pattern) (ha : d53177 p = 1) (hb : d61013 p = 1) : d61177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53172 q = 1) (hb : d53776 q = 1) : d61172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53172, d53776, d61172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53172, d53776, d61172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1450 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53175 q = 1) (hb : d53777 q = 1) : d61173 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53175, d53777, d61173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53175, d53777, d61173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53176 q = 1) (hb : d53778 q = 1) : d61174 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53176, d53778, d61174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53176, d53778, d61174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d53177 q = 1) (hb : d53779 q = 1) : d61175 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53177, d53779, d61175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53177, d53779, d61175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d53177 q = 1) (hb : d53780 q = 1) : d61176 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d61176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53780, d61176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53177 q = 1) (hb : d61013 q = 1) : d61177 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61013, d61177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61013, d61177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1452 (p : Pattern) (ha : d60389 p = 1) (hb : d61019 p = 1) : d61183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60384 q = 1) (hb : d61014 q = 1) : d61178 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60384, d61014, d61178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60384, d61014, d61178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1451 q ha hb
  have h2 (q : Pattern) (ha : d60385 q = 1) (hb : d61015 q = 1) : d61179 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60385, d61015, d61179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60385, d61015, d61179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60386 q = 1) (hb : d61016 q = 1) : d61180 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60386, d61016, d61180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60386, d61016, d61180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60387 q = 1) (hb : d61017 q = 1) : d61181 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60387, d61017, d61181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60387, d61017, d61181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60388 q = 1) (hb : d61018 q = 1) : d61182 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60388, d61018, d61182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60388, d61018, d61182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60389 q = 1) (hb : d61019 q = 1) : d61183 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60389, d61019, d61183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60389, d61019, d61183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1453 (p : Pattern) (ha : d53488 p = 1) (hb : d53805 p = 1) : d61193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53396 q = 1) (hb : d53800 q = 1) : d61188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53396, d53800, d61188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1403 q hb ha
    | true =>
      simp only [d53396, d53800, d61188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1396 q hb ha
  have h3 (q : Pattern) (ha : d53462 q = 1) (hb : d53801 q = 1) : d61189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d53801, d61189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53462, d53801, d61189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53465 q = 1) (hb : d53802 q = 1) : d61190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53465, d53802, d61190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53465, d53802, d61190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53486 q = 1) (hb : d53803 q = 1) : d61191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53486, d53803, d61191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53486, d53803, d61191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53487 q = 1) (hb : d53804 q = 1) : d61192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53487, d53804, d61192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53487, d53804, d61192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53488 q = 1) (hb : d53805 q = 1) : d61193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53488, d53805, d61193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53488, d53805, d61193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1454 (p : Pattern) (ha : d53494 p = 1) (hb : d61024 p = 1) : d61199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53489 q = 1) (hb : d53806 q = 1) : d61194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53489, d53806, d61194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53489, d53806, d61194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1453 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53492 q = 1) (hb : d53807 q = 1) : d61195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53492, d53807, d61195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53492, d53807, d61195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53493 q = 1) (hb : d53808 q = 1) : d61196 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53493, d53808, d61196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53493, d53808, d61196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d53494 q = 1) (hb : d53809 q = 1) : d61197 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53494, d53809, d61197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53494, d53809, d61197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d53494 q = 1) (hb : d53810 q = 1) : d61198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d61198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53810, d61198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53494 q = 1) (hb : d61024 q = 1) : d61199 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61024, d61199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61024, d61199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1455 (p : Pattern) (ha : d60399 p = 1) (hb : d61030 p = 1) : d61205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60394 q = 1) (hb : d61025 q = 1) : d61200 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60394, d61025, d61200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60394, d61025, d61200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1454 q ha hb
  have h2 (q : Pattern) (ha : d60395 q = 1) (hb : d61026 q = 1) : d61201 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60395, d61026, d61201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60395, d61026, d61201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60396 q = 1) (hb : d61027 q = 1) : d61202 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60396, d61027, d61202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60396, d61027, d61202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60397 q = 1) (hb : d61028 q = 1) : d61203 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60397, d61028, d61203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60397, d61028, d61203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60398 q = 1) (hb : d61029 q = 1) : d61204 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60398, d61029, d61204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60398, d61029, d61204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60399 q = 1) (hb : d61030 q = 1) : d61205 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60399, d61030, d61205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60399, d61030, d61205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1456 (p : Pattern) (ha : d60405 p = 1) (hb : d61036 p = 1) : d61211 p = 1 := by
  have h0 (q : Pattern) (ha : d60366 q = 1) (hb : d60993 q = 1) : d61124 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60366, d60993, d61124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1440 q ha hb
    | true =>
      simp only [d60366, d60993, d61124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1443 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60373 q = 1) (hb : d61001 q = 1) : d61143 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60373, d61001, d61143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60373, d61001, d61143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1446 q ha hb
  have h3 (q : Pattern) (ha : d60374 q = 1) (hb : d61002 q = 1) : d61144 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60374, d61002, d61144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60374, d61002, d61144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60381 q = 1) (hb : d61010 q = 1) : d61163 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60381, d61010, d61163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60381, d61010, d61163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1449 q ha hb
  have h5 (q : Pattern) (ha : d60382 q = 1) (hb : d61011 q = 1) : d61164 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60382, d61011, d61164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60382, d61011, d61164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60383 q = 1) (hb : d61012 q = 1) : d61165 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60383, d61012, d61165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60383, d61012, d61165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60390 q = 1) (hb : d61020 q = 1) : d61184 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60390, d61020, d61184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60390, d61020, d61184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1452 q ha hb
  have h8 (q : Pattern) (ha : d60391 q = 1) (hb : d61021 q = 1) : d61185 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60391, d61021, d61185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60391, d61021, d61185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60392 q = 1) (hb : d61022 q = 1) : d61186 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60392, d61022, d61186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60392, d61022, d61186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d60393 q = 1) (hb : d61023 q = 1) : d61187 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60393, d61023, d61187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d60393, d61023, d61187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d60400 q = 1) (hb : d61031 q = 1) : d61206 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60400, d61031, d61206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60400, d61031, d61206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1455 q ha hb
  have h12 (q : Pattern) (ha : d60401 q = 1) (hb : d61032 q = 1) : d61207 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60401, d61032, d61207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60401, d61032, d61207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d60402 q = 1) (hb : d61033 q = 1) : d61208 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60402, d61033, d61208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60402, d61033, d61208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d60403 q = 1) (hb : d61034 q = 1) : d61209 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60403, d61034, d61209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60403, d61034, d61209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d60404 q = 1) (hb : d61035 q = 1) : d61210 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d60404, d61035, d61210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d60404, d61035, d61210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d60405 q = 1) (hb : d61036 q = 1) : d61211 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d60405, d61036, d61211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d60405, d61036, d61211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro1457 (p : Pattern) (ha : d60411 p = 1) (hb : d61042 p = 1) : d61217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60406 q = 1) (hb : d61037 q = 1) : d61212 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d60406, d61037, d61212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1456 q ha hb
    | true =>
      simp only [d60406, d61037, d61212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60407 q = 1) (hb : d61038 q = 1) : d61213 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d60407, d61038, d61213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60407, d61038, d61213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60408 q = 1) (hb : d61039 q = 1) : d61214 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d60408, d61039, d61214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60408, d61039, d61214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60409 q = 1) (hb : d61040 q = 1) : d61215 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d60409, d61040, d61215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60409, d61040, d61215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60410 q = 1) (hb : d61041 q = 1) : d61216 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d60410, d61041, d61216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60410, d61041, d61216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60411 q = 1) (hb : d61042 q = 1) : d61217 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d60411, d61042, d61217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60411, d61042, d61217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1458 (p : Pattern) (ha : d60417 p = 1) (hb : d61048 p = 1) : d61223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60412 q = 1) (hb : d61043 q = 1) : d61218 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d60412, d61043, d61218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1457 q ha hb
    | true =>
      simp only [d60412, d61043, d61218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60413 q = 1) (hb : d61044 q = 1) : d61219 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d60413, d61044, d61219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60413, d61044, d61219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60414 q = 1) (hb : d61045 q = 1) : d61220 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d60414, d61045, d61220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60414, d61045, d61220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60415 q = 1) (hb : d61046 q = 1) : d61221 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d60415, d61046, d61221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60415, d61046, d61221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60416 q = 1) (hb : d61047 q = 1) : d61222 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d60416, d61047, d61222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60416, d61047, d61222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60417 q = 1) (hb : d61048 q = 1) : d61223 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d60417, d61048, d61223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60417, d61048, d61223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1459 (p : Pattern) (ha : d60423 p = 1) (hb : d61054 p = 1) : d61229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60418 q = 1) (hb : d61049 q = 1) : d61224 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d60418, d61049, d61224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1458 q ha hb
    | true =>
      simp only [d60418, d61049, d61224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60419 q = 1) (hb : d61050 q = 1) : d61225 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d60419, d61050, d61225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60419, d61050, d61225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60420 q = 1) (hb : d61051 q = 1) : d61226 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d60420, d61051, d61226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60420, d61051, d61226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60421 q = 1) (hb : d61052 q = 1) : d61227 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d60421, d61052, d61227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60421, d61052, d61227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60422 q = 1) (hb : d61053 q = 1) : d61228 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d60422, d61053, d61228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60422, d61053, d61228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60423 q = 1) (hb : d61054 q = 1) : d61229 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d60423, d61054, d61229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60423, d61054, d61229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1460 (p : Pattern) (ha : d60429 p = 1) (hb : d61060 p = 1) : d61235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60424 q = 1) (hb : d61055 q = 1) : d61230 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d60424, d61055, d61230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1459 q ha hb
    | true =>
      simp only [d60424, d61055, d61230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60425 q = 1) (hb : d61056 q = 1) : d61231 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d60425, d61056, d61231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60425, d61056, d61231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60426 q = 1) (hb : d61057 q = 1) : d61232 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d60426, d61057, d61232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60426, d61057, d61232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60427 q = 1) (hb : d61058 q = 1) : d61233 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d60427, d61058, d61233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60427, d61058, d61233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60428 q = 1) (hb : d61059 q = 1) : d61234 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d60428, d61059, d61234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60428, d61059, d61234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60429 q = 1) (hb : d61060 q = 1) : d61235 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d60429, d61060, d61235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60429, d61060, d61235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1461 (p : Pattern) (ha : d60435 p = 1) (hb : d61066 p = 1) : d61241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60430 q = 1) (hb : d61061 q = 1) : d61236 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d60430, d61061, d61236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1460 q ha hb
    | true =>
      simp only [d60430, d61061, d61236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60431 q = 1) (hb : d61062 q = 1) : d61237 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d60431, d61062, d61237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60431, d61062, d61237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60432 q = 1) (hb : d61063 q = 1) : d61238 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d60432, d61063, d61238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60432, d61063, d61238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60433 q = 1) (hb : d61064 q = 1) : d61239 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d60433, d61064, d61239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60433, d61064, d61239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60434 q = 1) (hb : d61065 q = 1) : d61240 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d60434, d61065, d61240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60434, d61065, d61240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60435 q = 1) (hb : d61066 q = 1) : d61241 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d60435, d61066, d61241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60435, d61066, d61241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1462 (p : Pattern) (ha : d60441 p = 1) (hb : d61072 p = 1) : d61247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60436 q = 1) (hb : d61067 q = 1) : d61242 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d60436, d61067, d61242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1461 q ha hb
    | true =>
      simp only [d60436, d61067, d61242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60437 q = 1) (hb : d61068 q = 1) : d61243 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d60437, d61068, d61243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60437, d61068, d61243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60438 q = 1) (hb : d61069 q = 1) : d61244 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d60438, d61069, d61244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60438, d61069, d61244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60439 q = 1) (hb : d61070 q = 1) : d61245 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d60439, d61070, d61245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60439, d61070, d61245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60440 q = 1) (hb : d61071 q = 1) : d61246 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d60440, d61071, d61246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60440, d61071, d61246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60441 q = 1) (hb : d61072 q = 1) : d61247 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d60441, d61072, d61247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60441, d61072, d61247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1463 (p : Pattern) (ha : d60447 p = 1) (hb : d61078 p = 1) : d61253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60442 q = 1) (hb : d61073 q = 1) : d61248 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d60442, d61073, d61248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1462 q ha hb
    | true =>
      simp only [d60442, d61073, d61248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d60443 q = 1) (hb : d61074 q = 1) : d61249 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d60443, d61074, d61249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60443, d61074, d61249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d60444 q = 1) (hb : d61075 q = 1) : d61250 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d60444, d61075, d61250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60444, d61075, d61250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d60445 q = 1) (hb : d61076 q = 1) : d61251 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d60445, d61076, d61251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60445, d61076, d61251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d60446 q = 1) (hb : d61077 q = 1) : d61252 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d60446, d61077, d61252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60446, d61077, d61252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d60447 q = 1) (hb : d61078 q = 1) : d61253 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d60447, d61078, d61253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d60447, d61078, d61253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro1464 (p : Pattern) (ha : d462 p = 1) (hb : d4349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d4340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d4341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d4342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d4343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d4349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1465 (p : Pattern) (ha : d4353 p = 1) (hb : d60973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d463 q = 1) (hb : d4350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d463, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1464 q ha hb
  have h3 (q : Pattern) (ha : d4351 q = 1) (hb : d53643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4351, d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d4352 q = 1) (hb : d53644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4352, d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4353 q = 1) (hb : d53645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4353, d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d4353 q = 1) (hb : d53646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d4353 q = 1) (hb : d60973 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro1466 (p : Pattern) (ha : d4385 p = 1) (hb : d53665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4376 q = 1) (hb : d53661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4376, d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4377 q = 1) (hb : d53662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4377, d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4378 q = 1) (hb : d53663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4379 q = 1) (hb : d53664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4385 q = 1) (hb : d53665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1467 (p : Pattern) (ha : d51670 p = 1) (hb : d60979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51670 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4386 q = 1) (hb : d53666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4386, d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1466 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51668 q = 1) (hb : d53667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51668, d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51669 q = 1) (hb : d53668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51669, d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51670 q = 1) (hb : d53669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51670, d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51670 q = 1) (hb : d53670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51670 q = 1) (hb : d60979 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1468 (p : Pattern) (ha : d60985 p = 1) (hb : d61264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d60245 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60974 q = 1) (hb : d61254 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60974, d61254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60974, d61254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1465 q hb ha
  have h3 (q : Pattern) (ha : d60975 q = 1) (hb : d61255 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60975, d61255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60975, d61255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60976 q = 1) (hb : d61256 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60976, d61256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60976, d61256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60977 q = 1) (hb : d61257 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60977, d61257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60977, d61257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60978 q = 1) (hb : d61258 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60978, d61258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60978, d61258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60980 q = 1) (hb : d61259 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60980, d61259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60980, d61259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1467 q hb ha
  have h8 (q : Pattern) (ha : d60981 q = 1) (hb : d61260 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60981, d61260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60981, d61260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60982 q = 1) (hb : d61261 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60982, d61261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60982, d61261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d60983 q = 1) (hb : d61262 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60983, d61262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60983, d61262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d60984 q = 1) (hb : d61263 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60984, d61263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60984, d61263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d60985 q = 1) (hb : d61264 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60985, d61264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d60985, d61264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro1469 (p : Pattern) (ha : d4422 p = 1) (hb : d53691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4413 q = 1) (hb : d53687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4413, d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4414 q = 1) (hb : d53688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4414, d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4415 q = 1) (hb : d53689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4416 q = 1) (hb : d53690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4422 q = 1) (hb : d53691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1470 (p : Pattern) (ha : d51695 p = 1) (hb : d60986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4423 q = 1) (hb : d53692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4423, d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1469 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51693 q = 1) (hb : d53693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51693, d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51694 q = 1) (hb : d53694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51694, d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51695 q = 1) (hb : d53695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51695, d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51695 q = 1) (hb : d53696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51695 q = 1) (hb : d60986 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1471 (p : Pattern) (ha : d60992 p = 1) (hb : d61270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60987 q = 1) (hb : d61265 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60987, d61265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60987, d61265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1470 q hb ha
  have h2 (q : Pattern) (ha : d60988 q = 1) (hb : d61266 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60988, d61266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60988, d61266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60989 q = 1) (hb : d61267 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60989, d61267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60989, d61267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60990 q = 1) (hb : d61268 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60990, d61268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60990, d61268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60991 q = 1) (hb : d61269 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60991, d61269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60991, d61269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60992 q = 1) (hb : d61270 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60992, d61270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60992, d61270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1472 (p : Pattern) (ha : d4460 p = 1) (hb : d53718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4451 q = 1) (hb : d53714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4451, d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4452 q = 1) (hb : d53715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4452, d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4453 q = 1) (hb : d53716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4454 q = 1) (hb : d53717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4460 q = 1) (hb : d53718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1473 (p : Pattern) (ha : d51721 p = 1) (hb : d60994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4461 q = 1) (hb : d53719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4461, d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1472 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51719 q = 1) (hb : d53720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51719, d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51720 q = 1) (hb : d53721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51720, d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51721 q = 1) (hb : d53722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51721, d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51721 q = 1) (hb : d53723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51721 q = 1) (hb : d60994 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1474 (p : Pattern) (ha : d61000 p = 1) (hb : d61277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60995 q = 1) (hb : d61272 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60995, d61272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60995, d61272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1473 q hb ha
  have h2 (q : Pattern) (ha : d60996 q = 1) (hb : d61273 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60996, d61273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60996, d61273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d60997 q = 1) (hb : d61274 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60997, d61274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60997, d61274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60998 q = 1) (hb : d61275 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60998, d61275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60998, d61275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60999 q = 1) (hb : d61276 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60999, d61276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60999, d61276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61000 q = 1) (hb : d61277 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61000, d61277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61000, d61277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1475 (p : Pattern) (ha : d4499 p = 1) (hb : d53746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d53742 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4490, d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4491 q = 1) (hb : d53743 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4491, d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4492 q = 1) (hb : d53744 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4493 q = 1) (hb : d53745 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4499 q = 1) (hb : d53746 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1476 (p : Pattern) (ha : d51748 p = 1) (hb : d61003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4500 q = 1) (hb : d53747 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4500, d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1475 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51746 q = 1) (hb : d53748 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51746, d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51747 q = 1) (hb : d53749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51747, d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51748 q = 1) (hb : d53750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51748, d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51748 q = 1) (hb : d53751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51748 q = 1) (hb : d61003 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1477 (p : Pattern) (ha : d61009 p = 1) (hb : d61285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61004 q = 1) (hb : d61280 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61004, d61280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61004, d61280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1476 q hb ha
  have h2 (q : Pattern) (ha : d61005 q = 1) (hb : d61281 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61005, d61281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61005, d61281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61006 q = 1) (hb : d61282 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61006, d61282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61006, d61282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61007 q = 1) (hb : d61283 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61007, d61283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61007, d61283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61008 q = 1) (hb : d61284 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61008, d61284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61008, d61284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61009 q = 1) (hb : d61285 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61009, d61285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61009, d61285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1478 (p : Pattern) (ha : d4539 p = 1) (hb : d53775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d53771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4530, d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4531 q = 1) (hb : d53772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4531, d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4532 q = 1) (hb : d53773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4533 q = 1) (hb : d53774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4539 q = 1) (hb : d53775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1479 (p : Pattern) (ha : d51776 p = 1) (hb : d61013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4540 q = 1) (hb : d53776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4540, d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1478 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51774 q = 1) (hb : d53777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51774, d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51775 q = 1) (hb : d53778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51775, d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51776 q = 1) (hb : d53779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51776, d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51776 q = 1) (hb : d53780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51776 q = 1) (hb : d61013 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1480 (p : Pattern) (ha : d61019 p = 1) (hb : d61294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61014 q = 1) (hb : d61289 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61014, d61289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61014, d61289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1479 q hb ha
  have h2 (q : Pattern) (ha : d61015 q = 1) (hb : d61290 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61015, d61290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61015, d61290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61016 q = 1) (hb : d61291 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61016, d61291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61016, d61291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61017 q = 1) (hb : d61292 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61017, d61292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61017, d61292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61018 q = 1) (hb : d61293 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61018, d61293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61018, d61293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61019 q = 1) (hb : d61294 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61019, d61294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61019, d61294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1481 (p : Pattern) (ha : d4580 p = 1) (hb : d53805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d53801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4571, d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4572 q = 1) (hb : d53802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4572, d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4573 q = 1) (hb : d53803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4574 q = 1) (hb : d53804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4580 q = 1) (hb : d53805 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1482 (p : Pattern) (ha : d51805 p = 1) (hb : d61024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4581 q = 1) (hb : d53806 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4581, d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1481 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51803 q = 1) (hb : d53807 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51803, d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d51804 q = 1) (hb : d53808 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51804, d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51805 q = 1) (hb : d53809 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51805, d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51805 q = 1) (hb : d53810 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51805 q = 1) (hb : d61024 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro1483 (p : Pattern) (ha : d61030 p = 1) (hb : d61304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61025 q = 1) (hb : d61299 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61025, d61299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61025, d61299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1482 q hb ha
  have h2 (q : Pattern) (ha : d61026 q = 1) (hb : d61300 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61026, d61300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61026, d61300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61027 q = 1) (hb : d61301 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61027, d61301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61027, d61301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61028 q = 1) (hb : d61302 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61028, d61302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61028, d61302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61029 q = 1) (hb : d61303 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61029, d61303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61029, d61303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61030 q = 1) (hb : d61304 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61030, d61304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61030, d61304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1484 (p : Pattern) (ha : d61036 p = 1) (hb : d61310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d60993 q = 1) (hb : d61271 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60993, d61271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1468 q ha hb
    | true =>
      simp only [d60993, d61271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1471 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61001 q = 1) (hb : d61278 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61001, d61278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61001, d61278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1474 q ha hb
  have h3 (q : Pattern) (ha : d61002 q = 1) (hb : d61279 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61002, d61279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61002, d61279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61010 q = 1) (hb : d61286 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61010, d61286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61010, d61286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1477 q ha hb
  have h5 (q : Pattern) (ha : d61011 q = 1) (hb : d61287 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61011, d61287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61011, d61287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61012 q = 1) (hb : d61288 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61012, d61288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61012, d61288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61020 q = 1) (hb : d61295 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61020, d61295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61020, d61295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1480 q ha hb
  have h8 (q : Pattern) (ha : d61021 q = 1) (hb : d61296 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61021, d61296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61021, d61296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61022 q = 1) (hb : d61297 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61022, d61297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61022, d61297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61023 q = 1) (hb : d61298 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61023, d61298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61023, d61298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61031 q = 1) (hb : d61305 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61031, d61305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61031, d61305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1483 q ha hb
  have h12 (q : Pattern) (ha : d61032 q = 1) (hb : d61306 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61032, d61306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61032, d61306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61033 q = 1) (hb : d61307 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61033, d61307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61033, d61307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61034 q = 1) (hb : d61308 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61034, d61308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61034, d61308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61035 q = 1) (hb : d61309 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61035, d61309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61035, d61309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61036 q = 1) (hb : d61310 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61036, d61310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61036, d61310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro1485 (p : Pattern) (ha : d61042 p = 1) (hb : d61316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61037 q = 1) (hb : d61311 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61037, d61311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1484 q ha hb
    | true =>
      simp only [d61037, d61311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61038 q = 1) (hb : d61312 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61038, d61312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61038, d61312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61039 q = 1) (hb : d61313 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61039, d61313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61039, d61313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61040 q = 1) (hb : d61314 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61040, d61314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61040, d61314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61041 q = 1) (hb : d61315 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61041, d61315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61041, d61315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61042 q = 1) (hb : d61316 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61042, d61316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61042, d61316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1486 (p : Pattern) (ha : d61048 p = 1) (hb : d61322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61043 q = 1) (hb : d61317 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61043, d61317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1485 q ha hb
    | true =>
      simp only [d61043, d61317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61044 q = 1) (hb : d61318 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61044, d61318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61044, d61318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61045 q = 1) (hb : d61319 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61045, d61319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61045, d61319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61046 q = 1) (hb : d61320 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61046, d61320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61046, d61320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61047 q = 1) (hb : d61321 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61047, d61321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61047, d61321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61048 q = 1) (hb : d61322 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61048, d61322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61048, d61322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1487 (p : Pattern) (ha : d61054 p = 1) (hb : d61328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61049 q = 1) (hb : d61323 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61049, d61323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1486 q ha hb
    | true =>
      simp only [d61049, d61323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61050 q = 1) (hb : d61324 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61050, d61324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61050, d61324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61051 q = 1) (hb : d61325 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61051, d61325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61051, d61325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61052 q = 1) (hb : d61326 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61052, d61326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61052, d61326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61053 q = 1) (hb : d61327 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61053, d61327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61053, d61327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61054 q = 1) (hb : d61328 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61054, d61328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61054, d61328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1488 (p : Pattern) (ha : d61060 p = 1) (hb : d61334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61055 q = 1) (hb : d61329 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61055, d61329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1487 q ha hb
    | true =>
      simp only [d61055, d61329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61056 q = 1) (hb : d61330 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61056, d61330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61056, d61330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61057 q = 1) (hb : d61331 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61057, d61331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61057, d61331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61058 q = 1) (hb : d61332 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61058, d61332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61058, d61332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61059 q = 1) (hb : d61333 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61059, d61333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61059, d61333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61060 q = 1) (hb : d61334 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61060, d61334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61060, d61334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1489 (p : Pattern) (ha : d61066 p = 1) (hb : d61340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61061 q = 1) (hb : d61335 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61061, d61335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1488 q ha hb
    | true =>
      simp only [d61061, d61335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61062 q = 1) (hb : d61336 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61062, d61336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61062, d61336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61063 q = 1) (hb : d61337 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61063, d61337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61063, d61337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61064 q = 1) (hb : d61338 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61064, d61338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61064, d61338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61065 q = 1) (hb : d61339 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61065, d61339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61065, d61339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61066 q = 1) (hb : d61340 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61066, d61340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61066, d61340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1490 (p : Pattern) (ha : d61072 p = 1) (hb : d61346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61067 q = 1) (hb : d61341 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61067, d61341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1489 q ha hb
    | true =>
      simp only [d61067, d61341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61068 q = 1) (hb : d61342 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61068, d61342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61068, d61342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61069 q = 1) (hb : d61343 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61069, d61343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61069, d61343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61070 q = 1) (hb : d61344 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61070, d61344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61070, d61344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61071 q = 1) (hb : d61345 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61071, d61345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61071, d61345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61072 q = 1) (hb : d61346 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61072, d61346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61072, d61346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1491 (p : Pattern) (ha : d61078 p = 1) (hb : d61352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61073 q = 1) (hb : d61347 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61073, d61347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1490 q ha hb
    | true =>
      simp only [d61073, d61347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61074 q = 1) (hb : d61348 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61074, d61348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61074, d61348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61075 q = 1) (hb : d61349 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61075, d61349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61075, d61349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61076 q = 1) (hb : d61350 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61076, d61350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61076, d61350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61077 q = 1) (hb : d61351 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61077, d61351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61077, d61351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61078 q = 1) (hb : d61352 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61078, d61352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61078, d61352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro1492 (p : Pattern) (ha : d95 p = 1) (hb : d61359 p = 1) : d3324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d48 q = 1) : d48 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d55 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d56 q = 1) (hb : d61357 q = 1) : d3319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d61357, d3319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d56, d61357, d3319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d57 q = 1) (hb : d61357 q = 1) : d3320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58 q = 1) (hb : d61357 q = 1) : d3321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d59 q = 1) (hb : d61357 q = 1) : d3322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d60 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d61 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d62 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d63 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d64 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d65 q = 1) (hb : d61357 q = 1) : d3323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d89 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d90 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d90, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d91 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d91, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d92 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h21 (q : Pattern) (ha : d94 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h22 (q : Pattern) (ha : d95 q = 1) (hb : d61359 q = 1) : d3324 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d61359, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d95, d61359, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro1493 (p : Pattern) (ha : d51652 p = 1) (hb : d61359 p = 1) : d61544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d105 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d104 q = 1) : d104 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112 q = 1) (hb : d61357 q = 1) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113 q = 1) (hb : d61357 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d114 q = 1) (hb : d61357 q = 1) : d3331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114, d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51643 q = 1) : d51643 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51647 q = 1) (hb : d61357 q = 1) : d61539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d61357, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51647, d61357, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d214 q = 1) (hb : d61357 q = 1) : d214 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d51648 q = 1) (hb : d61357 q = 1) : d61540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51648, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51649 q = 1) (hb : d61357 q = 1) : d61541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51649, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d51650 q = 1) (hb : d61357 q = 1) : d61542 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51650, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4349 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4350 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4351 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4352 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h21 (q : Pattern) (ha : d4353 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d51651 q = 1) (hb : d61357 q = 1) : d61543 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51651, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4359 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4360 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d4361 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4361, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4362 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d4363 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h30 (q : Pattern) (ha : d4364 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h31 (q : Pattern) (ha : d51652 q = 1) (hb : d61359 q = 1) : d61544 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d61359, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d51652, d61359, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro1494 (p : Pattern) (ha : d51676 p = 1) (hb : d61359 p = 1) : d61555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d285 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d284 q = 1) : d284 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d291 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292 q = 1) (hb : d61357 q = 1) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d293 q = 1) (hb : d61357 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d294 q = 1) (hb : d61357 q = 1) : d3345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d294, d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51660 q = 1) : d51660 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51664 q = 1) (hb : d61357 q = 1) : d61550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d61357, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51664, d61357, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d397 q = 1) : d397 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d398 q = 1) (hb : d61357 q = 1) : d3347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d61357, d3347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d398, d61357, d3347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51665 q = 1) (hb : d61357 q = 1) : d61551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51665, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51666 q = 1) (hb : d61357 q = 1) : d61552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51666, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51667 q = 1) (hb : d61357 q = 1) : d61553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51667, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4385 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4386 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d407 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51668 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51669 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51670 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51671 q = 1) (hb : d61357 q = 1) : d61554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51671, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4395 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4396 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51672 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51672, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51672, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51673 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51674 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51675 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51676 q = 1) (hb : d61359 q = 1) : d61555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51676, d61359, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51676, d61359, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1495 (p : Pattern) (ha : d51682 p = 1) (hb : d61359 p = 1) : d61561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d61359 q = 1) : d3325 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1492 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d61359 q = 1) : d3326 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d61359 q = 1) : d3327 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d61359 q = 1) : d3328 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d61359 q = 1) : d61545 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1493 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d61359 q = 1) : d61546 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d61359 q = 1) : d61547 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d61359 q = 1) : d61548 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d61359 q = 1) : d61549 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51677 q = 1) (hb : d61359 q = 1) : d61556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51677, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51677, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1494 q ha hb
  have h11 (q : Pattern) (ha : d51678 q = 1) (hb : d61359 q = 1) : d61557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51678, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51678, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51679 q = 1) (hb : d61359 q = 1) : d61558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51679, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51679, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51680 q = 1) (hb : d61359 q = 1) : d61559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51680, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51680, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51681 q = 1) (hb : d61359 q = 1) : d61560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51681, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51681, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51682 q = 1) (hb : d61359 q = 1) : d61561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51682, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51682, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro1496 (p : Pattern) (ha : d51701 p = 1) (hb : d61359 p = 1) : d61567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d498 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d499 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d497 q = 1) : d497 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d507 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d508 q = 1) (hb : d61357 q = 1) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d509 q = 1) (hb : d61357 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d509, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d510 q = 1) (hb : d61357 q = 1) : d3361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d510, d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51685 q = 1) : d51685 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51689 q = 1) (hb : d61357 q = 1) : d61562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d61357, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51689, d61357, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d638 q = 1) : d638 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d644 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d645 q = 1) (hb : d61357 q = 1) : d3363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d61357, d3363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d645, d61357, d3363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51690 q = 1) (hb : d61357 q = 1) : d61563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51690, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51691 q = 1) (hb : d61357 q = 1) : d61564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51691, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51692 q = 1) (hb : d61357 q = 1) : d61565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51692, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4422 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4423 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d653 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d654 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51693 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51694 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51695 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51696 q = 1) (hb : d61357 q = 1) : d61566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51696, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4432 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4433 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51697 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51697, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51697, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51698 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51699 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51700 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51701 q = 1) (hb : d61359 q = 1) : d61567 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51701, d61359, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51701, d61359, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1497 (p : Pattern) (ha : d51707 p = 1) (hb : d61359 p = 1) : d61573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51702 q = 1) (hb : d61359 q = 1) : d61568 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51702, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51702, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1496 q ha hb
  have h2 (q : Pattern) (ha : d51703 q = 1) (hb : d61359 q = 1) : d61569 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51703, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51703, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51704 q = 1) (hb : d61359 q = 1) : d61570 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51704, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51704, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51705 q = 1) (hb : d61359 q = 1) : d61571 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51705, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51705, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51706 q = 1) (hb : d61359 q = 1) : d61572 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51706, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51706, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51707 q = 1) (hb : d61359 q = 1) : d61573 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51707, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51707, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro1498 (p : Pattern) (ha : d51727 p = 1) (hb : d61359 p = 1) : d61580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d790 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d791 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d789 q = 1) : d789 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d799 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d800 q = 1) (hb : d61357 q = 1) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d801 q = 1) (hb : d61357 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d801, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d802 q = 1) (hb : d61357 q = 1) : d3378 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d802, d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51711 q = 1) : d51711 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51715 q = 1) (hb : d61357 q = 1) : d61575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d61357, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51715, d61357, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d944 q = 1) : d944 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d950 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d951 q = 1) (hb : d61357 q = 1) : d3380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d61357, d3380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d951, d61357, d3380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d51716 q = 1) (hb : d61357 q = 1) : d61576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51716, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51717 q = 1) (hb : d61357 q = 1) : d61577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51717, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d51718 q = 1) (hb : d61357 q = 1) : d61578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51718, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d4460 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d4461 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d959 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d960 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d51719 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d51720 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d51720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d51721 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d51722 q = 1) (hb : d61357 q = 1) : d61579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51722, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d4470 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d4471 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d51723 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51723, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d51723, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h32 (q : Pattern) (ha : d51724 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51725 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d51725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h34 (q : Pattern) (ha : d51726 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d51726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h35 (q : Pattern) (ha : d51727 q = 1) (hb : d61359 q = 1) : d61580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51727, d61359, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51727, d61359, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro1499 (p : Pattern) (ha : d51733 p = 1) (hb : d61359 p = 1) : d61586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51728 q = 1) (hb : d61359 q = 1) : d61581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51728, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51728, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1498 q ha hb
  have h2 (q : Pattern) (ha : d51729 q = 1) (hb : d61359 q = 1) : d61582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51729, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51729, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51730 q = 1) (hb : d61359 q = 1) : d61583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51730, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51730, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51731 q = 1) (hb : d61359 q = 1) : d61584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51731, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51731, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51732 q = 1) (hb : d61359 q = 1) : d61585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51732, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51732, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51733 q = 1) (hb : d61359 q = 1) : d61586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51733, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51733, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
