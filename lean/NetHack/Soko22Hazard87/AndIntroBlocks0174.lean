import NetHack.Soko22Hazard87.AndIntroBlocks0173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro43500 (p : Pattern) (ha : d101955 p = 1) (hb : d132474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101950 q = 1) (hb : d132469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101950, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43499 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101951 q = 1) (hb : d132470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101952 q = 1) (hb : d132471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101953 q = 1) (hb : d132472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101954 q = 1) (hb : d132473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101955 q = 1) (hb : d132474 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101955, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43501 (p : Pattern) (ha : d101961 p = 1) (hb : d132480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101956 q = 1) (hb : d132475 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101956, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43500 q ha hb
  have h2 (q : Pattern) (ha : d101957 q = 1) (hb : d132476 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101957, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101958 q = 1) (hb : d132477 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101958, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101959 q = 1) (hb : d132478 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101959, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101960 q = 1) (hb : d132479 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101960, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101961 q = 1) (hb : d132480 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101961, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43502 (p : Pattern) (ha : d101969 p = 1) (hb : d132497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101965 q = 1) (hb : d132493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101965, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10307 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101966 q = 1) (hb : d132494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101966, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101967 q = 1) (hb : d132495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101967, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101968 q = 1) (hb : d132496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101968, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101969 q = 1) (hb : d132497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101969, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43503 (p : Pattern) (ha : d101975 p = 1) (hb : d132503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101970 q = 1) (hb : d132498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101970, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43502 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10323 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101971 q = 1) (hb : d132499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101972 q = 1) (hb : d132500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101973 q = 1) (hb : d132501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101974 q = 1) (hb : d132502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101975 q = 1) (hb : d132503 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101975, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43504 (p : Pattern) (ha : d101981 p = 1) (hb : d132509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101976 q = 1) (hb : d132504 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101976, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43503 q ha hb
  have h2 (q : Pattern) (ha : d101977 q = 1) (hb : d132505 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101977, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101978 q = 1) (hb : d132506 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101978, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101979 q = 1) (hb : d132507 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101979, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101980 q = 1) (hb : d132508 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101980, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101981 q = 1) (hb : d132509 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101981, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43505 (p : Pattern) (ha : d101990 p = 1) (hb : d132527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132522 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101986 q = 1) (hb : d132523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101986, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101987 q = 1) (hb : d132524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101987, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101988 q = 1) (hb : d132525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101988, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101989 q = 1) (hb : d132526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101989, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101990 q = 1) (hb : d132527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101990, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43506 (p : Pattern) (ha : d101996 p = 1) (hb : d132533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101991 q = 1) (hb : d132528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101991, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43505 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101992 q = 1) (hb : d132529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101993 q = 1) (hb : d132530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101994 q = 1) (hb : d132531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101995 q = 1) (hb : d132532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101996 q = 1) (hb : d132533 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101996, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43507 (p : Pattern) (ha : d102002 p = 1) (hb : d132539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101997 q = 1) (hb : d132534 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101997, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43506 q ha hb
  have h2 (q : Pattern) (ha : d101998 q = 1) (hb : d132535 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101998, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101999 q = 1) (hb : d132536 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101999, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102000 q = 1) (hb : d132537 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102000, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102001 q = 1) (hb : d132538 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102001, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102002 q = 1) (hb : d132539 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102002, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43508 (p : Pattern) (ha : d102008 p = 1) (hb : d132545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101925 q = 1) (hb : d132434 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43492 q ha hb
    | true =>
      simp only [d101925, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43495 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101943 q = 1) (hb : d132453 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101943, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43498 q ha hb
  have h3 (q : Pattern) (ha : d101944 q = 1) (hb : d132454 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101962 q = 1) (hb : d132481 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101962, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43501 q ha hb
  have h5 (q : Pattern) (ha : d101963 q = 1) (hb : d132482 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101963, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101964 q = 1) (hb : d132483 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101982 q = 1) (hb : d132510 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101982, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43504 q ha hb
  have h8 (q : Pattern) (ha : d101983 q = 1) (hb : d132511 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101983, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101984 q = 1) (hb : d132512 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101984, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101985 q = 1) (hb : d132513 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102003 q = 1) (hb : d132540 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102003, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43507 q ha hb
  have h12 (q : Pattern) (ha : d102004 q = 1) (hb : d132541 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102004, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102005 q = 1) (hb : d132542 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102005, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102006 q = 1) (hb : d132543 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102006, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102007 q = 1) (hb : d132544 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102008 q = 1) (hb : d132545 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro43509 (p : Pattern) (ha : d102014 p = 1) (hb : d132551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102009 q = 1) (hb : d132546 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43508 q ha hb
    | true =>
      simp only [d102009, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102010 q = 1) (hb : d132547 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102011 q = 1) (hb : d132548 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102012 q = 1) (hb : d132549 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102013 q = 1) (hb : d132550 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102014 q = 1) (hb : d132551 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43510 (p : Pattern) (ha : d102020 p = 1) (hb : d132557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102015 q = 1) (hb : d132552 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43509 q ha hb
    | true =>
      simp only [d102015, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102016 q = 1) (hb : d132553 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102017 q = 1) (hb : d132554 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102018 q = 1) (hb : d132555 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102019 q = 1) (hb : d132556 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102020 q = 1) (hb : d132557 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43511 (p : Pattern) (ha : d102026 p = 1) (hb : d132563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102021 q = 1) (hb : d132558 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43510 q ha hb
    | true =>
      simp only [d102021, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102022 q = 1) (hb : d132559 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102023 q = 1) (hb : d132560 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102024 q = 1) (hb : d132561 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102025 q = 1) (hb : d132562 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102025, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102026 q = 1) (hb : d132563 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102026, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43512 (p : Pattern) (ha : d102032 p = 1) (hb : d132569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102027 q = 1) (hb : d132564 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43511 q ha hb
    | true =>
      simp only [d102027, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102028 q = 1) (hb : d132565 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102029 q = 1) (hb : d132566 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102030 q = 1) (hb : d132567 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102031 q = 1) (hb : d132568 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102032 q = 1) (hb : d132569 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43513 (p : Pattern) (ha : d102038 p = 1) (hb : d132575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d132570 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43512 q ha hb
    | true =>
      simp only [d102033, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102034 q = 1) (hb : d132571 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102035 q = 1) (hb : d132572 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102036 q = 1) (hb : d132573 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102037 q = 1) (hb : d132574 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102038 q = 1) (hb : d132575 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43514 (p : Pattern) (ha : d102044 p = 1) (hb : d132581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d132576 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43513 q ha hb
    | true =>
      simp only [d102039, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d132577 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d132578 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d132579 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d132580 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d132581 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43515 (p : Pattern) (ha : d102050 p = 1) (hb : d132587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d132582 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43514 q ha hb
    | true =>
      simp only [d102045, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d132583 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d132584 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d132585 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d132586 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d132587 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43516 (p : Pattern) (ha : d132763 p = 1) (hb : d188524 p = 1) : d132763 p = 1 := by
  have h0 (q : Pattern) (ha : d132763 q = 1) (hb : d188524 q = 1) : d132763 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro43517 (p : Pattern) (ha : d187878 p = 1) (hb : d188524 p = 1) : d187878 p = 1 := by
  have h0 (q : Pattern) (ha : d187878 q = 1) (hb : d188524 q = 1) : d187878 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro43518 (p : Pattern) (ha : d19742 p = 1) (hb : d129672 p = 1) : d9302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19738 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19739 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19740 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19741 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9301 q = 1) (hb : d129672 q = 1) : d9301 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19742 q = 1) (hb : d129672 q = 1) : d9302 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19742, d9302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19742, d9302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43519 (p : Pattern) (ha : d19748 p = 1) (hb : d129672 p = 1) : d9308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19743 q = 1) (hb : d129672 q = 1) : d9303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43518 q ha hb
    | true =>
      simp only [d19743, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19744 q = 1) (hb : d129672 q = 1) : d9304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19745 q = 1) (hb : d129672 q = 1) : d9305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19745, d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19745, d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19746 q = 1) (hb : d129672 q = 1) : d9306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19746, d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19746, d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19747 q = 1) (hb : d129672 q = 1) : d9307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19747, d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19747, d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19748 q = 1) (hb : d129672 q = 1) : d9308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19748, d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19748, d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43520 (p : Pattern) (ha : d19754 p = 1) (hb : d129672 p = 1) : d9314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43519 q ha hb
    | true =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19750 q = 1) (hb : d129672 q = 1) : d9310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19750, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19751 q = 1) (hb : d129672 q = 1) : d9311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19751, d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19751, d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19752 q = 1) (hb : d129672 q = 1) : d9312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19752, d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19752, d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19753 q = 1) (hb : d129672 q = 1) : d9313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19753, d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19753, d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19754 q = 1) (hb : d129672 q = 1) : d9314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19754, d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19754, d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43521 (p : Pattern) (ha : d19760 p = 1) (hb : d129672 p = 1) : d9320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19755 q = 1) (hb : d129672 q = 1) : d9315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19755, d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19755, d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43520 q ha hb
  have h2 (q : Pattern) (ha : d19756 q = 1) (hb : d129672 q = 1) : d9316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19756, d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19756, d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19757 q = 1) (hb : d129672 q = 1) : d9317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19757, d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19757, d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19758 q = 1) (hb : d129672 q = 1) : d9318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19758, d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19758, d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19759 q = 1) (hb : d129672 q = 1) : d9319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19759, d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19759, d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19760 q = 1) (hb : d129672 q = 1) : d9320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19760, d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19760, d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43522 (p : Pattern) (ha : d19769 p = 1) (hb : d129672 p = 1) : d9335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19765 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19766 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9297 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19738 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19739 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19767 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19740 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19768 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9334 q = 1) (hb : d129672 q = 1) : d9334 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19769 q = 1) (hb : d129672 q = 1) : d9335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19769, d9335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19769, d9335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43523 (p : Pattern) (ha : d19775 p = 1) (hb : d129672 p = 1) : d9341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43522 q ha hb
    | true =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19743 q = 1) (hb : d129672 q = 1) : d9303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43518 q ha hb
    | true =>
      simp only [d19743, d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19744 q = 1) (hb : d129672 q = 1) : d9304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19772 q = 1) (hb : d129672 q = 1) : d9338 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19772, d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19772, d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19773 q = 1) (hb : d129672 q = 1) : d9339 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19773, d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19773, d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19774 q = 1) (hb : d129672 q = 1) : d9340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19774, d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19774, d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19775 q = 1) (hb : d129672 q = 1) : d9341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19775, d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19775, d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43524 (p : Pattern) (ha : d129672 p = 1) (hb : d130215 p = 1) : d101879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d129672 q = 1) : d9342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43523 q ha hb
    | true =>
      simp only [d19776, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43519 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130211 q = 1) : d101875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130211, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130211, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19749 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43519 q ha hb
    | true =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19750 q = 1) (hb : d129672 q = 1) : d9310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19750, d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130212 q = 1) : d101876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130212, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130212, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130213 q = 1) : d101877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130213, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130213, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130214 q = 1) : d101878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130214, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130214, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130215 q = 1) : d101879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130215, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130215, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43525 (p : Pattern) (ha : d129672 p = 1) (hb : d130221 p = 1) : d101885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130216 q = 1) : d101880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130216, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130216, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43524 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130217 q = 1) : d101881 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130217, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130217, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130218 q = 1) : d101882 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130218, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130218, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130219 q = 1) : d101883 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130219, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130219, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130220 q = 1) : d101884 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130220, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130220, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130221 q = 1) : d101885 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130221, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130221, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43526 (p : Pattern) (ha : d19845 p = 1) (hb : d129672 p = 1) : d9436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d129672 q = 1) : d9309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43519 q ha hb
    | true =>
      simp only [d19749, d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19841 q = 1) (hb : d129672 q = 1) : d9432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19841, d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19842 q = 1) (hb : d129672 q = 1) : d9433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19842, d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19843 q = 1) (hb : d129672 q = 1) : d9434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19844 q = 1) (hb : d129672 q = 1) : d9435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19845 q = 1) (hb : d129672 q = 1) : d9436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43527 (p : Pattern) (ha : d19809 p = 1) (hb : d129672 p = 1) : d9394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19805 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19806 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9330 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19765 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19766 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19807 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9297 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19738 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19738, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19739 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19767 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19808 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9393 q = 1) (hb : d129672 q = 1) : d9393 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19809 q = 1) (hb : d129672 q = 1) : d9394 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19809, d9394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19809, d9394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43528 (p : Pattern) (ha : d19815 p = 1) (hb : d129672 p = 1) : d9400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19810 q = 1) (hb : d129672 q = 1) : d9395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19810, d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43527 q ha hb
    | true =>
      simp only [d19810, d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19811 q = 1) (hb : d129672 q = 1) : d9396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19811, d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19811, d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19770 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43522 q ha hb
    | true =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19771 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19812 q = 1) (hb : d129672 q = 1) : d9397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19812, d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19812, d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19813 q = 1) (hb : d129672 q = 1) : d9398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19813, d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19813, d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19814 q = 1) (hb : d129672 q = 1) : d9399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19814, d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19814, d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19815 q = 1) (hb : d129672 q = 1) : d9400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19815, d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19815, d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43529 (p : Pattern) (ha : d19833 p = 1) (hb : d129672 p = 1) : d9424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d129672 q = 1) : d9336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43522 q ha hb
    | true =>
      simp only [d19770, d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d129672 q = 1) : d9337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19830 q = 1) (hb : d129672 q = 1) : d9421 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19830, d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19830, d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19831 q = 1) (hb : d129672 q = 1) : d9422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19831, d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19831, d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19832 q = 1) (hb : d129672 q = 1) : d9423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19832, d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19832, d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19833 q = 1) (hb : d129672 q = 1) : d9424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19833, d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19833, d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43530 (p : Pattern) (ha : d129672 p = 1) (hb : d130231 p = 1) : d101895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19816 q = 1) (hb : d129672 q = 1) : d9401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19816, d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43528 q ha hb
    | true =>
      simp only [d19816, d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43523 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130227 q = 1) : d101891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130227, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130227, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19834 q = 1) (hb : d129672 q = 1) : d9425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19834, d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43529 q ha hb
    | true =>
      simp only [d19834, d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19835 q = 1) (hb : d129672 q = 1) : d9426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19835, d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19835, d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130228 q = 1) : d101892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130228, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130228, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130229 q = 1) : d101893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130229, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130229, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130230 q = 1) : d101894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130230, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130230, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130231 q = 1) : d101895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130231, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130231, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43531 (p : Pattern) (ha : d129672 p = 1) (hb : d130237 p = 1) : d101901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130232 q = 1) : d101896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130232, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130232, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43530 q ha hb
  have h2 (q : Pattern) (ha : d19846 q = 1) (hb : d129672 q = 1) : d9437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43526 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130233 q = 1) : d101897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130233, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130233, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130234 q = 1) : d101898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130234, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130234, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130235 q = 1) : d101899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130235, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130235, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130236 q = 1) : d101900 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130236, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130236, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130237 q = 1) : d101901 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130237, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130237, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43532 (p : Pattern) (ha : d129672 p = 1) (hb : d130243 p = 1) : d101907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19761 q = 1) (hb : d129672 q = 1) : d9321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19761, d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19761, d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43521 q ha hb
  have h2 (q : Pattern) (ha : d19762 q = 1) (hb : d129672 q = 1) : d9322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19762, d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19762, d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19763 q = 1) (hb : d129672 q = 1) : d9323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19763, d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19763, d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19764 q = 1) (hb : d129672 q = 1) : d9324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19764, d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19764, d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130222 q = 1) : d101886 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130222, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130222, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43525 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130223 q = 1) : d101887 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130223, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130223, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130224 q = 1) : d101888 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130224, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130224, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130225 q = 1) : d101889 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130225, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130225, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d130226 q = 1) : d101890 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130226, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130226, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d130238 q = 1) : d101902 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130238, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130238, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43531 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d130239 q = 1) : d101903 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130239, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130239, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d130240 q = 1) : d101904 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130240, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130240, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d130241 q = 1) : d101905 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130241, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130241, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d130242 q = 1) : d101906 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130242, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130242, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d130243 q = 1) : d101907 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130243, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130243, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43533 (p : Pattern) (ha : d19877 p = 1) (hb : d129672 p = 1) : d9497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19765 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19766 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19867 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19876 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9496 q = 1) (hb : d129672 q = 1) : d9496 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19877 q = 1) (hb : d129672 q = 1) : d9497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19877, d9497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19877, d9497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43534 (p : Pattern) (ha : d19921 p = 1) (hb : d129672 p = 1) : d9556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19878 q = 1) (hb : d129672 q = 1) : d9498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43533 q ha hb
    | true =>
      simp only [d19878, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19879 q = 1) (hb : d129672 q = 1) : d9499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19918 q = 1) (hb : d129672 q = 1) : d9553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19918, d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19918, d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19919 q = 1) (hb : d129672 q = 1) : d9554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19919, d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19919, d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19920 q = 1) (hb : d129672 q = 1) : d9555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19920, d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19920, d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19921 q = 1) (hb : d129672 q = 1) : d9556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19921, d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19921, d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43535 (p : Pattern) (ha : d19927 p = 1) (hb : d129672 p = 1) : d9562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19922 q = 1) (hb : d129672 q = 1) : d9557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19922, d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43534 q ha hb
    | true =>
      simp only [d19922, d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19923 q = 1) (hb : d129672 q = 1) : d9558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19923, d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19923, d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19924 q = 1) (hb : d129672 q = 1) : d9559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19924, d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19924, d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19925 q = 1) (hb : d129672 q = 1) : d9560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19925, d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19925, d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19926 q = 1) (hb : d129672 q = 1) : d9561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19926, d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19926, d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19927 q = 1) (hb : d129672 q = 1) : d9562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19927, d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19927, d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43536 (p : Pattern) (ha : d19864 p = 1) (hb : d129672 p = 1) : d9484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9475 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19858 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19858, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19858, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19859 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9479 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19860 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19860, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19860, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19861 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19862 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19805 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19806 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9330 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19765 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d19766 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19807 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19863 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9483 q = 1) (hb : d129672 q = 1) : d9483 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d19864 q = 1) (hb : d129672 q = 1) : d9484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19864, d9484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19864, d9484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43537 (p : Pattern) (ha : d19869 p = 1) (hb : d129672 p = 1) : d9489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19805 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19805, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19806 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9330 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19765 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19766 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19807 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19867 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19868 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9488 q = 1) (hb : d129672 q = 1) : d9488 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19869 q = 1) (hb : d129672 q = 1) : d9489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19869, d9489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19869, d9489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43538 (p : Pattern) (ha : d19875 p = 1) (hb : d129672 p = 1) : d9495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19865 q = 1) (hb : d129672 q = 1) : d9485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19865, d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43536 q ha hb
    | true =>
      simp only [d19865, d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19866 q = 1) (hb : d129672 q = 1) : d9486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19866, d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19866, d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19870 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43537 q ha hb
    | true =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19871 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19872 q = 1) (hb : d129672 q = 1) : d9492 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19872, d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19872, d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19873 q = 1) (hb : d129672 q = 1) : d9493 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19873, d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19873, d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19874 q = 1) (hb : d129672 q = 1) : d9494 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19874, d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19874, d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19875 q = 1) (hb : d129672 q = 1) : d9495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19875, d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19875, d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43539 (p : Pattern) (ha : d19883 p = 1) (hb : d129672 p = 1) : d9503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43537 q ha hb
    | true =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19878 q = 1) (hb : d129672 q = 1) : d9498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43533 q ha hb
    | true =>
      simp only [d19878, d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19879 q = 1) (hb : d129672 q = 1) : d9499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19880 q = 1) (hb : d129672 q = 1) : d9500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19880, d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19880, d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19881 q = 1) (hb : d129672 q = 1) : d9501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19881, d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19881, d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19882 q = 1) (hb : d129672 q = 1) : d9502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19882, d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19882, d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19883 q = 1) (hb : d129672 q = 1) : d9503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19883, d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19883, d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43540 (p : Pattern) (ha : d19910 p = 1) (hb : d129672 p = 1) : d9545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d129672 q = 1) : d9490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43537 q ha hb
    | true =>
      simp only [d19870, d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d129672 q = 1) : d9491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19907 q = 1) (hb : d129672 q = 1) : d9542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19907, d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19907, d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19908 q = 1) (hb : d129672 q = 1) : d9543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19908, d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19908, d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19909 q = 1) (hb : d129672 q = 1) : d9544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19909, d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19909, d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19910 q = 1) (hb : d129672 q = 1) : d9545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19910, d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19910, d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43541 (p : Pattern) (ha : d129672 p = 1) (hb : d130248 p = 1) : d101912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19884 q = 1) (hb : d129672 q = 1) : d9504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19884, d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43538 q ha hb
    | true =>
      simp only [d19884, d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43539 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130244 q = 1) : d101908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130244, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130244, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19911 q = 1) (hb : d129672 q = 1) : d9546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19911, d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43540 q ha hb
    | true =>
      simp only [d19911, d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19912 q = 1) (hb : d129672 q = 1) : d9547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19912, d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19912, d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130245 q = 1) : d101909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130245, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130245, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130246 q = 1) : d101910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130246, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130246, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130247 q = 1) : d101911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130247, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130247, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130248 q = 1) : d101912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130248, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130248, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43542 (p : Pattern) (ha : d129672 p = 1) (hb : d130254 p = 1) : d101918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130249 q = 1) : d101913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130249, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130249, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43541 q ha hb
  have h2 (q : Pattern) (ha : d19928 q = 1) (hb : d129672 q = 1) : d9563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19928, d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19928, d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43535 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130250 q = 1) : d101914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130250, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130250, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130251 q = 1) : d101915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130251, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130251, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130252 q = 1) : d101916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130252, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130252, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130253 q = 1) : d101917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130253, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130253, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130254 q = 1) : d101918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130254, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130254, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43543 (p : Pattern) (ha : d129672 p = 1) (hb : d130260 p = 1) : d101924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130255 q = 1) : d101919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130255, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130255, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43542 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130256 q = 1) : d101920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130256, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130256, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130257 q = 1) : d101921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130257, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130257, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130258 q = 1) : d101922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130258, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130258, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130259 q = 1) : d101923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130259, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130259, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130260 q = 1) : d101924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130260, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130260, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43544 (p : Pattern) (ha : d19965 p = 1) (hb : d129672 p = 1) : d9642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19948 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19949 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19955 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19964 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9641 q = 1) (hb : d129672 q = 1) : d9641 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19965 q = 1) (hb : d129672 q = 1) : d9642 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19965, d9642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19965, d9642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43545 (p : Pattern) (ha : d20011 p = 1) (hb : d129672 p = 1) : d9725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19966 q = 1) (hb : d129672 q = 1) : d9643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43544 q ha hb
    | true =>
      simp only [d19966, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19967 q = 1) (hb : d129672 q = 1) : d9644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20008 q = 1) (hb : d129672 q = 1) : d9722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20008, d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20008, d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20009 q = 1) (hb : d129672 q = 1) : d9723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20009, d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20009, d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20010 q = 1) (hb : d129672 q = 1) : d9724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20010, d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20010, d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20011 q = 1) (hb : d129672 q = 1) : d9725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20011, d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20011, d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43546 (p : Pattern) (ha : d20017 p = 1) (hb : d129672 p = 1) : d9731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20012 q = 1) (hb : d129672 q = 1) : d9726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20012, d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43545 q ha hb
    | true =>
      simp only [d20012, d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20013 q = 1) (hb : d129672 q = 1) : d9727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20013, d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20013, d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20014 q = 1) (hb : d129672 q = 1) : d9728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20014, d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20014, d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20015 q = 1) (hb : d129672 q = 1) : d9729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20015, d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20015, d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20016 q = 1) (hb : d129672 q = 1) : d9730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20016, d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20016, d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20017 q = 1) (hb : d129672 q = 1) : d9731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20017, d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20017, d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43547 (p : Pattern) (ha : d19952 p = 1) (hb : d129672 p = 1) : d9629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9609 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19941 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19941, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19941, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19942 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19943 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19943, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19943, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19944 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19945 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9620 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19946 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19946, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19947 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9624 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19948 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d19949 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19950 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19951 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9628 q = 1) (hb : d129672 q = 1) : d9628 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d19952 q = 1) (hb : d129672 q = 1) : d9629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19952, d9629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19952, d9629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43548 (p : Pattern) (ha : d19957 p = 1) (hb : d129672 p = 1) : d9634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19946 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19946, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19947 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9624 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19948 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19948, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19949 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19950 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19955 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19956 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9633 q = 1) (hb : d129672 q = 1) : d9633 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19957 q = 1) (hb : d129672 q = 1) : d9634 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19957, d9634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19957, d9634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43549 (p : Pattern) (ha : d19963 p = 1) (hb : d129672 p = 1) : d9640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19953 q = 1) (hb : d129672 q = 1) : d9630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19953, d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43547 q ha hb
    | true =>
      simp only [d19953, d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19954 q = 1) (hb : d129672 q = 1) : d9631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19954, d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19954, d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19958 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43548 q ha hb
    | true =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19959 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19960 q = 1) (hb : d129672 q = 1) : d9637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19960, d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19960, d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19961 q = 1) (hb : d129672 q = 1) : d9638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19961, d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19961, d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19962 q = 1) (hb : d129672 q = 1) : d9639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19962, d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19962, d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19963 q = 1) (hb : d129672 q = 1) : d9640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19963, d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19963, d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43550 (p : Pattern) (ha : d19971 p = 1) (hb : d129672 p = 1) : d9648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43548 q ha hb
    | true =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19966 q = 1) (hb : d129672 q = 1) : d9643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43544 q ha hb
    | true =>
      simp only [d19966, d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19967 q = 1) (hb : d129672 q = 1) : d9644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19968 q = 1) (hb : d129672 q = 1) : d9645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19968, d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19968, d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19969 q = 1) (hb : d129672 q = 1) : d9646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19969, d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19969, d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19970 q = 1) (hb : d129672 q = 1) : d9647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19970, d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19970, d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19971 q = 1) (hb : d129672 q = 1) : d9648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19971, d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19971, d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43551 (p : Pattern) (ha : d20000 p = 1) (hb : d129672 p = 1) : d9714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d129672 q = 1) : d9635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43548 q ha hb
    | true =>
      simp only [d19958, d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d129672 q = 1) : d9636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19997 q = 1) (hb : d129672 q = 1) : d9711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19997, d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19997, d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19998 q = 1) (hb : d129672 q = 1) : d9712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19998, d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19998, d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19999 q = 1) (hb : d129672 q = 1) : d9713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19999, d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19999, d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20000 q = 1) (hb : d129672 q = 1) : d9714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20000, d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20000, d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43552 (p : Pattern) (ha : d129672 p = 1) (hb : d130266 p = 1) : d101930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19972 q = 1) (hb : d129672 q = 1) : d9649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19972, d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43549 q ha hb
    | true =>
      simp only [d19972, d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43550 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130262 q = 1) : d101926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130262, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130262, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20001 q = 1) (hb : d129672 q = 1) : d9715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20001, d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43551 q ha hb
    | true =>
      simp only [d20001, d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20002 q = 1) (hb : d129672 q = 1) : d9716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20002, d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20002, d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130263 q = 1) : d101927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130263, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130263, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130264 q = 1) : d101928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130264, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130264, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130265 q = 1) : d101929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130265, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130265, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130266 q = 1) : d101930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130266, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130266, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43553 (p : Pattern) (ha : d129672 p = 1) (hb : d130272 p = 1) : d101936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130267 q = 1) : d101931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130267, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130267, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43552 q ha hb
  have h2 (q : Pattern) (ha : d20018 q = 1) (hb : d129672 q = 1) : d9732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20018, d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20018, d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43546 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130268 q = 1) : d101932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130268, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130268, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130269 q = 1) : d101933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130269, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130269, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130270 q = 1) : d101934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130270, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130270, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130271 q = 1) : d101935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130271, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130271, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130272 q = 1) : d101936 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130272, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130272, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43554 (p : Pattern) (ha : d129672 p = 1) (hb : d130278 p = 1) : d101942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130273 q = 1) : d101937 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130273, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130273, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43553 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130274 q = 1) : d101938 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130274, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130274, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130275 q = 1) : d101939 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130275, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130275, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130276 q = 1) : d101940 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130276, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130276, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130277 q = 1) : d101941 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130277, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130277, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130278 q = 1) : d101942 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130278, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130278, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43555 (p : Pattern) (ha : d20059 p = 1) (hb : d129672 p = 1) : d9875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9870 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20055 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20055, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20056 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20057 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20058 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9874 q = 1) (hb : d129672 q = 1) : d9874 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20059 q = 1) (hb : d129672 q = 1) : d9875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20059, d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20059, d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43556 (p : Pattern) (ha : d20114 p = 1) (hb : d129672 p = 1) : d10010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20060 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43555 q ha hb
    | true =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20061 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20111 q = 1) (hb : d129672 q = 1) : d10007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20111, d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20111, d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20112 q = 1) (hb : d129672 q = 1) : d10008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20112, d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20112, d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20113 q = 1) (hb : d129672 q = 1) : d10009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20113, d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20113, d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20114 q = 1) (hb : d129672 q = 1) : d10010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20114, d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20114, d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43557 (p : Pattern) (ha : d20120 p = 1) (hb : d129672 p = 1) : d10016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20115 q = 1) (hb : d129672 q = 1) : d10011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20115, d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43556 q ha hb
    | true =>
      simp only [d20115, d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20116 q = 1) (hb : d129672 q = 1) : d10012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20116, d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20116, d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20117 q = 1) (hb : d129672 q = 1) : d10013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20117, d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20117, d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20118 q = 1) (hb : d129672 q = 1) : d10014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20118, d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20118, d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20119 q = 1) (hb : d129672 q = 1) : d10015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20119, d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20119, d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20120 q = 1) (hb : d129672 q = 1) : d10016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20120, d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20120, d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43558 (p : Pattern) (ha : d20043 p = 1) (hb : d129672 p = 1) : d9856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20032 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20032, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20032, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20033 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9822 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20034 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20034, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20035 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20036 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9834 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9851 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d20040 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20041 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20042 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9855 q = 1) (hb : d129672 q = 1) : d9855 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20043 q = 1) (hb : d129672 q = 1) : d9856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20043, d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20043, d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43559 (p : Pattern) (ha : d20048 p = 1) (hb : d129672 p = 1) : d9861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9851 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20040 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20041 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20046 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20047 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9860 q = 1) (hb : d129672 q = 1) : d9860 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20048 q = 1) (hb : d129672 q = 1) : d9861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20048, d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20048, d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43560 (p : Pattern) (ha : d20054 p = 1) (hb : d129672 p = 1) : d9867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20044 q = 1) (hb : d129672 q = 1) : d9857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20044, d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43558 q ha hb
    | true =>
      simp only [d20044, d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20045 q = 1) (hb : d129672 q = 1) : d9858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20045, d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20045, d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20049 q = 1) (hb : d129672 q = 1) : d9862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43559 q ha hb
    | true =>
      simp only [d20049, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20050 q = 1) (hb : d129672 q = 1) : d9863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20051 q = 1) (hb : d129672 q = 1) : d9864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20051, d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20051, d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20052 q = 1) (hb : d129672 q = 1) : d9865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20052, d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20052, d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20053 q = 1) (hb : d129672 q = 1) : d9866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20053, d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20053, d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20054 q = 1) (hb : d129672 q = 1) : d9867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20054, d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20054, d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43561 (p : Pattern) (ha : d20065 p = 1) (hb : d129672 p = 1) : d9881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20049 q = 1) (hb : d129672 q = 1) : d9862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43559 q ha hb
    | true =>
      simp only [d20049, d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20050 q = 1) (hb : d129672 q = 1) : d9863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43555 q ha hb
    | true =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20062 q = 1) (hb : d129672 q = 1) : d9878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20062, d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20062, d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20063 q = 1) (hb : d129672 q = 1) : d9879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20063, d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20063, d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20064 q = 1) (hb : d129672 q = 1) : d9880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20064, d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20064, d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20065 q = 1) (hb : d129672 q = 1) : d9881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20065, d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20065, d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43562 (p : Pattern) (ha : d20097 p = 1) (hb : d129672 p = 1) : d9993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9851 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20040 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20041 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9988 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20093 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20093, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20093, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20094 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20095 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20096 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9992 q = 1) (hb : d129672 q = 1) : d9992 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20097 q = 1) (hb : d129672 q = 1) : d9993 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20097, d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20097, d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43563 (p : Pattern) (ha : d20103 p = 1) (hb : d129672 p = 1) : d9999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20098 q = 1) (hb : d129672 q = 1) : d9994 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20098, d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43562 q ha hb
    | true =>
      simp only [d20098, d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20099 q = 1) (hb : d129672 q = 1) : d9995 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20099, d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20099, d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20100 q = 1) (hb : d129672 q = 1) : d9996 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20100, d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20100, d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20101 q = 1) (hb : d129672 q = 1) : d9997 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20101, d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20101, d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20102 q = 1) (hb : d129672 q = 1) : d9998 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20102, d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20102, d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20103 q = 1) (hb : d129672 q = 1) : d9999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20103, d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20103, d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43564 (p : Pattern) (ha : d129672 p = 1) (hb : d130285 p = 1) : d101949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20066 q = 1) (hb : d129672 q = 1) : d9882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20066, d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43560 q ha hb
    | true =>
      simp only [d20066, d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43561 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130281 q = 1) : d101945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130281, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130281, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20104 q = 1) (hb : d129672 q = 1) : d10000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20104, d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43563 q ha hb
    | true =>
      simp only [d20104, d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20105 q = 1) (hb : d129672 q = 1) : d10001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20105, d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20105, d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130282 q = 1) : d101946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130282, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130282, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130283 q = 1) : d101947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130283, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130283, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130284 q = 1) : d101948 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130284, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130284, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130285 q = 1) : d101949 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130285, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130285, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43565 (p : Pattern) (ha : d129672 p = 1) (hb : d130291 p = 1) : d101955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130286 q = 1) : d101950 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130286, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130286, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43564 q ha hb
  have h2 (q : Pattern) (ha : d20121 q = 1) (hb : d129672 q = 1) : d10017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20121, d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20121, d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43557 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130287 q = 1) : d101951 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130287, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130287, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130288 q = 1) : d101952 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130288, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130288, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130289 q = 1) : d101953 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130289, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130289, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130290 q = 1) : d101954 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130290, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130290, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130291 q = 1) : d101955 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130291, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130291, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43566 (p : Pattern) (ha : d129672 p = 1) (hb : d130297 p = 1) : d101961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130292 q = 1) : d101956 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130292, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130292, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43565 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130293 q = 1) : d101957 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130293, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130293, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130294 q = 1) : d101958 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130294, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130294, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130295 q = 1) : d101959 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130295, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130295, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130296 q = 1) : d101960 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130296, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130296, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130297 q = 1) : d101961 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130297, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130297, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43567 (p : Pattern) (ha : d20163 p = 1) (hb : d129672 p = 1) : d10169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20159 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20159, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20160 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20161 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20162 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10168 q = 1) (hb : d129672 q = 1) : d10168 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20163 q = 1) (hb : d129672 q = 1) : d10169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20163, d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20163, d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43568 (p : Pattern) (ha : d20218 p = 1) (hb : d129672 p = 1) : d10316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20164 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43567 q ha hb
    | true =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20165 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20215 q = 1) (hb : d129672 q = 1) : d10313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20215, d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20215, d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20216 q = 1) (hb : d129672 q = 1) : d10314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20216, d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20216, d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20217 q = 1) (hb : d129672 q = 1) : d10315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20217, d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20217, d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20218 q = 1) (hb : d129672 q = 1) : d10316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20218, d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20218, d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43569 (p : Pattern) (ha : d20224 p = 1) (hb : d129672 p = 1) : d10322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20219 q = 1) (hb : d129672 q = 1) : d10317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20219, d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43568 q ha hb
    | true =>
      simp only [d20219, d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20220 q = 1) (hb : d129672 q = 1) : d10318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20220, d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20220, d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20221 q = 1) (hb : d129672 q = 1) : d10319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20221, d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20221, d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20222 q = 1) (hb : d129672 q = 1) : d10320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20222, d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20222, d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20223 q = 1) (hb : d129672 q = 1) : d10321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20223, d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20223, d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20224 q = 1) (hb : d129672 q = 1) : d10322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20224, d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20224, d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43570 (p : Pattern) (ha : d20147 p = 1) (hb : d129672 p = 1) : d10147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20136 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20136, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20136, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20137 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10107 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20138 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20138, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20138, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20139 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20140 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10122 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20141 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20142 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10142 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20143 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d20144 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20145 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20146 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10146 q = 1) (hb : d129672 q = 1) : d10146 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20147 q = 1) (hb : d129672 q = 1) : d10147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20147, d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20147, d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43571 (p : Pattern) (ha : d20152 p = 1) (hb : d129672 p = 1) : d10152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10142 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20143 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20144 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20145 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20150 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20151 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10151 q = 1) (hb : d129672 q = 1) : d10151 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20152 q = 1) (hb : d129672 q = 1) : d10152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20152, d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20152, d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43572 (p : Pattern) (ha : d20158 p = 1) (hb : d129672 p = 1) : d10158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20148 q = 1) (hb : d129672 q = 1) : d10148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20148, d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43570 q ha hb
    | true =>
      simp only [d20148, d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20149 q = 1) (hb : d129672 q = 1) : d10149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20149, d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20149, d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20153 q = 1) (hb : d129672 q = 1) : d10153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43571 q ha hb
    | true =>
      simp only [d20153, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20154 q = 1) (hb : d129672 q = 1) : d10154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20155 q = 1) (hb : d129672 q = 1) : d10155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20155, d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20155, d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20156 q = 1) (hb : d129672 q = 1) : d10156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20156, d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20156, d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20157 q = 1) (hb : d129672 q = 1) : d10157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20157, d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20157, d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20158 q = 1) (hb : d129672 q = 1) : d10158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20158, d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20158, d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43573 (p : Pattern) (ha : d20169 p = 1) (hb : d129672 p = 1) : d10175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20153 q = 1) (hb : d129672 q = 1) : d10153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43571 q ha hb
    | true =>
      simp only [d20153, d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20154 q = 1) (hb : d129672 q = 1) : d10154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43567 q ha hb
    | true =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20166 q = 1) (hb : d129672 q = 1) : d10172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20166, d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20166, d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20167 q = 1) (hb : d129672 q = 1) : d10173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20167, d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20167, d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20168 q = 1) (hb : d129672 q = 1) : d10174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20168, d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20168, d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20169 q = 1) (hb : d129672 q = 1) : d10175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20169, d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20169, d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43574 (p : Pattern) (ha : d20201 p = 1) (hb : d129672 p = 1) : d10299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10142 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20143 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20144 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20145 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10294 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20197 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20197, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20197, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20198 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20199 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20200 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10298 q = 1) (hb : d129672 q = 1) : d10298 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20201 q = 1) (hb : d129672 q = 1) : d10299 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20201, d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20201, d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43575 (p : Pattern) (ha : d20207 p = 1) (hb : d129672 p = 1) : d10305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20202 q = 1) (hb : d129672 q = 1) : d10300 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20202, d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43574 q ha hb
    | true =>
      simp only [d20202, d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20203 q = 1) (hb : d129672 q = 1) : d10301 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20203, d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20203, d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20204 q = 1) (hb : d129672 q = 1) : d10302 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20204, d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20204, d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20205 q = 1) (hb : d129672 q = 1) : d10303 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20205, d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20205, d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20206 q = 1) (hb : d129672 q = 1) : d10304 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20206, d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20206, d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20207 q = 1) (hb : d129672 q = 1) : d10305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20207, d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20207, d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43576 (p : Pattern) (ha : d129672 p = 1) (hb : d130305 p = 1) : d101969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20170 q = 1) (hb : d129672 q = 1) : d10176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20170, d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43572 q ha hb
    | true =>
      simp only [d20170, d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43573 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130301 q = 1) : d101965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130301, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130301, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20208 q = 1) (hb : d129672 q = 1) : d10306 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20208, d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43575 q ha hb
    | true =>
      simp only [d20208, d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20209 q = 1) (hb : d129672 q = 1) : d10307 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20209, d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20209, d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130302 q = 1) : d101966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130302, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130302, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130303 q = 1) : d101967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130303, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130303, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130304 q = 1) : d101968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130304, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130304, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130305 q = 1) : d101969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130305, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130305, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43577 (p : Pattern) (ha : d129672 p = 1) (hb : d130311 p = 1) : d101975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130306 q = 1) : d101970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130306, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130306, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43576 q ha hb
  have h2 (q : Pattern) (ha : d20225 q = 1) (hb : d129672 q = 1) : d10323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20225, d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20225, d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43569 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130307 q = 1) : d101971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130307, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130307, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130308 q = 1) : d101972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130308, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130308, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130309 q = 1) : d101973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130309, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130309, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130310 q = 1) : d101974 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130310, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130310, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130311 q = 1) : d101975 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130311, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130311, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43578 (p : Pattern) (ha : d129672 p = 1) (hb : d130317 p = 1) : d101981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130312 q = 1) : d101976 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130312, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130312, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43577 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130313 q = 1) : d101977 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130313, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130313, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130314 q = 1) : d101978 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130314, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130314, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130315 q = 1) : d101979 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130315, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130315, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130316 q = 1) : d101980 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130316, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130316, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130317 q = 1) : d101981 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130317, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130317, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43579 (p : Pattern) (ha : d20268 p = 1) (hb : d129672 p = 1) : d10446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20264 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20264, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20265 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20266 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20267 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10445 q = 1) (hb : d129672 q = 1) : d10445 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20268 q = 1) (hb : d129672 q = 1) : d10446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20268, d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20268, d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43580 (p : Pattern) (ha : d20323 p = 1) (hb : d129672 p = 1) : d10582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20269 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43579 q ha hb
    | true =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20270 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20320 q = 1) (hb : d129672 q = 1) : d10579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20320, d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20320, d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20321 q = 1) (hb : d129672 q = 1) : d10580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20321, d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20321, d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20322 q = 1) (hb : d129672 q = 1) : d10581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20322, d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20322, d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20323 q = 1) (hb : d129672 q = 1) : d10582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20323, d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20323, d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43581 (p : Pattern) (ha : d20329 p = 1) (hb : d129672 p = 1) : d10588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20324 q = 1) (hb : d129672 q = 1) : d10583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20324, d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43580 q ha hb
    | true =>
      simp only [d20324, d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20325 q = 1) (hb : d129672 q = 1) : d10584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20325, d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20325, d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20326 q = 1) (hb : d129672 q = 1) : d10585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20326, d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20326, d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20327 q = 1) (hb : d129672 q = 1) : d10586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20327, d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20327, d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20328 q = 1) (hb : d129672 q = 1) : d10587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20328, d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20328, d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20329 q = 1) (hb : d129672 q = 1) : d10588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20329, d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20329, d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43582 (p : Pattern) (ha : d20252 p = 1) (hb : d129672 p = 1) : d10424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10378 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20241 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20241, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20241, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20242 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20243 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20243, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20243, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20244 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20245 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20246 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20247 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10419 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20248 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d20249 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20250 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20251 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10423 q = 1) (hb : d129672 q = 1) : d10423 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d20252 q = 1) (hb : d129672 q = 1) : d10424 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20252, d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20252, d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43583 (p : Pattern) (ha : d20257 p = 1) (hb : d129672 p = 1) : d10429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20248 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20249 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20250 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20255 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20256 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10428 q = 1) (hb : d129672 q = 1) : d10428 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20257 q = 1) (hb : d129672 q = 1) : d10429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20257, d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20257, d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43584 (p : Pattern) (ha : d20263 p = 1) (hb : d129672 p = 1) : d10435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20253 q = 1) (hb : d129672 q = 1) : d10425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20253, d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43582 q ha hb
    | true =>
      simp only [d20253, d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20254 q = 1) (hb : d129672 q = 1) : d10426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20254, d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20254, d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20258 q = 1) (hb : d129672 q = 1) : d10430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43583 q ha hb
    | true =>
      simp only [d20258, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20259 q = 1) (hb : d129672 q = 1) : d10431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20260 q = 1) (hb : d129672 q = 1) : d10432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20260, d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20260, d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20261 q = 1) (hb : d129672 q = 1) : d10433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20261, d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20261, d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20262 q = 1) (hb : d129672 q = 1) : d10434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20262, d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20262, d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20263 q = 1) (hb : d129672 q = 1) : d10435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20263, d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20263, d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43585 (p : Pattern) (ha : d20274 p = 1) (hb : d129672 p = 1) : d10452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20258 q = 1) (hb : d129672 q = 1) : d10430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43583 q ha hb
    | true =>
      simp only [d20258, d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20259 q = 1) (hb : d129672 q = 1) : d10431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43579 q ha hb
    | true =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20271 q = 1) (hb : d129672 q = 1) : d10449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20271, d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20271, d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20272 q = 1) (hb : d129672 q = 1) : d10450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20272, d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20272, d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20273 q = 1) (hb : d129672 q = 1) : d10451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20273, d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20273, d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20274 q = 1) (hb : d129672 q = 1) : d10452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20274, d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20274, d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43586 (p : Pattern) (ha : d20306 p = 1) (hb : d129672 p = 1) : d10565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20248 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20249 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20250 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10560 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20302 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20302, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20302, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20303 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20304 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20305 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10564 q = 1) (hb : d129672 q = 1) : d10564 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20306 q = 1) (hb : d129672 q = 1) : d10565 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20306, d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20306, d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43587 (p : Pattern) (ha : d20312 p = 1) (hb : d129672 p = 1) : d10571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20307 q = 1) (hb : d129672 q = 1) : d10566 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20307, d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43586 q ha hb
    | true =>
      simp only [d20307, d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20308 q = 1) (hb : d129672 q = 1) : d10567 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20308, d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20308, d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20309 q = 1) (hb : d129672 q = 1) : d10568 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20309, d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20309, d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20310 q = 1) (hb : d129672 q = 1) : d10569 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20310, d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20310, d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20311 q = 1) (hb : d129672 q = 1) : d10570 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20311, d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20311, d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20312 q = 1) (hb : d129672 q = 1) : d10571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20312, d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20312, d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43588 (p : Pattern) (ha : d129672 p = 1) (hb : d130326 p = 1) : d101990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20275 q = 1) (hb : d129672 q = 1) : d10453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20275, d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43584 q ha hb
    | true =>
      simp only [d20275, d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43585 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130322 q = 1) : d101986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130322, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130322, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20313 q = 1) (hb : d129672 q = 1) : d10572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20313, d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43587 q ha hb
    | true =>
      simp only [d20313, d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20314 q = 1) (hb : d129672 q = 1) : d10573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20314, d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20314, d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130323 q = 1) : d101987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130323, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130323, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130324 q = 1) : d101988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130324, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130324, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130325 q = 1) : d101989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130325, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130325, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130326 q = 1) : d101990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130326, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130326, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43589 (p : Pattern) (ha : d129672 p = 1) (hb : d130332 p = 1) : d101996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130327 q = 1) : d101991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130327, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130327, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43588 q ha hb
  have h2 (q : Pattern) (ha : d20330 q = 1) (hb : d129672 q = 1) : d10589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20330, d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20330, d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43581 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130328 q = 1) : d101992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130328, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130328, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130329 q = 1) : d101993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130329, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130329, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130330 q = 1) : d101994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130330, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130330, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130331 q = 1) : d101995 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130331, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130331, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130332 q = 1) : d101996 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130332, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130332, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43590 (p : Pattern) (ha : d129672 p = 1) (hb : d130338 p = 1) : d102002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130333 q = 1) : d101997 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130333, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130333, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43589 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130334 q = 1) : d101998 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130334, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130334, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130335 q = 1) : d101999 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130335, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130335, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130336 q = 1) : d102000 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130336, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130336, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130337 q = 1) : d102001 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130337, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130337, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130338 q = 1) : d102002 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130338, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130338, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43591 (p : Pattern) (ha : d129672 p = 1) (hb : d130344 p = 1) : d102008 p = 1 := by
  have h0 (q : Pattern) (ha : d129672 q = 1) (hb : d130261 q = 1) : d101925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130261, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43532 q ha hb
    | true =>
      simp only [d130261, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43543 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130279 q = 1) : d101943 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130279, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130279, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43554 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130280 q = 1) : d101944 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130280, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130280, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130298 q = 1) : d101962 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130298, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130298, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43566 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130299 q = 1) : d101963 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130299, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130299, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130300 q = 1) : d101964 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130300, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130300, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d130318 q = 1) : d101982 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130318, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130318, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43578 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d130319 q = 1) : d101983 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130319, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130319, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d130320 q = 1) : d101984 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130320, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130320, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d130321 q = 1) : d101985 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130321, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130321, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d130339 q = 1) : d102003 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130339, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130339, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43590 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d130340 q = 1) : d102004 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130340, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130340, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d130341 q = 1) : d102005 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130341, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130341, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d130342 q = 1) : d102006 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130342, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130342, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d130343 q = 1) : d102007 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130343, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130343, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129672 q = 1) (hb : d130344 q = 1) : d102008 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130344, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130344, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43592 (p : Pattern) (ha : d129672 p = 1) (hb : d130350 p = 1) : d102014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130345 q = 1) : d102009 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130345, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43591 q ha hb
    | true =>
      simp only [d130345, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130346 q = 1) : d102010 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130346, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130346, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130347 q = 1) : d102011 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130347, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130347, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130348 q = 1) : d102012 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130348, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130348, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130349 q = 1) : d102013 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130349, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130349, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130350 q = 1) : d102014 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130350, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130350, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43593 (p : Pattern) (ha : d129672 p = 1) (hb : d130356 p = 1) : d102020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130351 q = 1) : d102015 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130351, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43592 q ha hb
    | true =>
      simp only [d130351, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130352 q = 1) : d102016 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130352, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130352, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130353 q = 1) : d102017 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130353, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130353, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130354 q = 1) : d102018 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130354, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130354, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130355 q = 1) : d102019 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130355, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130355, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130356 q = 1) : d102020 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130356, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130356, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43594 (p : Pattern) (ha : d129672 p = 1) (hb : d130362 p = 1) : d102026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130357 q = 1) : d102021 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130357, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43593 q ha hb
    | true =>
      simp only [d130357, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130358 q = 1) : d102022 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130358, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130358, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130359 q = 1) : d102023 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130359, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130359, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130360 q = 1) : d102024 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130360, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130360, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130361 q = 1) : d102025 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130361, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130361, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130362 q = 1) : d102026 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130362, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130362, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43595 (p : Pattern) (ha : d129672 p = 1) (hb : d130368 p = 1) : d102032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130363 q = 1) : d102027 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130363, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43594 q ha hb
    | true =>
      simp only [d130363, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130364 q = 1) : d102028 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130364, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130364, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130365 q = 1) : d102029 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130365, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130365, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130366 q = 1) : d102030 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130366, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130366, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130367 q = 1) : d102031 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130367, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130367, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130368 q = 1) : d102032 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130368, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130368, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43596 (p : Pattern) (ha : d129672 p = 1) (hb : d130374 p = 1) : d102038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130369 q = 1) : d102033 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130369, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43595 q ha hb
    | true =>
      simp only [d130369, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130370 q = 1) : d102034 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130370, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130370, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130371 q = 1) : d102035 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130371, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130371, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130372 q = 1) : d102036 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130372, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130372, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130373 q = 1) : d102037 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130373, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130373, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130374 q = 1) : d102038 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130374, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130374, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43597 (p : Pattern) (ha : d129672 p = 1) (hb : d130380 p = 1) : d102044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130375 q = 1) : d102039 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130375, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43596 q ha hb
    | true =>
      simp only [d130375, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130376 q = 1) : d102040 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130376, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130376, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130377 q = 1) : d102041 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130377, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130377, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130378 q = 1) : d102042 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130378, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130378, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130379 q = 1) : d102043 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130379, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130379, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130380 q = 1) : d102044 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130380, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130380, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43598 (p : Pattern) (ha : d129672 p = 1) (hb : d130386 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d130381 q = 1) : d102045 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130381, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43597 q ha hb
    | true =>
      simp only [d130381, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d130382 q = 1) : d102046 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130382, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130382, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d130383 q = 1) : d102047 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130383, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130383, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d130384 q = 1) : d102048 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130384, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130384, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d130385 q = 1) : d102049 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130385, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130385, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d130386 q = 1) : d102050 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130386, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130386, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43599 (p : Pattern) (ha : d9302 p = 1) (hb : d100953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9301 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9302 q = 1) (hb : d100953 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9302, d100953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9302, d100953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43600 (p : Pattern) (ha : d9308 p = 1) (hb : d100959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9303 q = 1) (hb : d100954 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d100954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43599 q ha hb
    | true =>
      simp only [d9303, d100954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9304 q = 1) (hb : d100955 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d100955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d100955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9305 q = 1) (hb : d100956 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9305, d100956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9305, d100956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9306 q = 1) (hb : d100957 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9306, d100957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9306, d100957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9307 q = 1) (hb : d100958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9307, d100958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9307, d100958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9308 q = 1) (hb : d100959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9308, d100959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9308, d100959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43601 (p : Pattern) (ha : d9314 p = 1) (hb : d100965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
    | true =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9310 q = 1) (hb : d100961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d100961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9310, d100961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9311 q = 1) (hb : d100962 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9311, d100962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9311, d100962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9312 q = 1) (hb : d100963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9312, d100963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9312, d100963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9313 q = 1) (hb : d100964 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9313, d100964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9313, d100964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9314 q = 1) (hb : d100965 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9314, d100965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9314, d100965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43602 (p : Pattern) (ha : d9320 p = 1) (hb : d100971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9315 q = 1) (hb : d100966 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9315, d100966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9315, d100966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43601 q ha hb
  have h2 (q : Pattern) (ha : d9316 q = 1) (hb : d100967 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9316, d100967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9316, d100967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9317 q = 1) (hb : d100968 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9317, d100968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9317, d100968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9318 q = 1) (hb : d100969 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9318, d100969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9318, d100969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9319 q = 1) (hb : d100970 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9319, d100970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9319, d100970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9320 q = 1) (hb : d100971 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9320, d100971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9320, d100971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43603 (p : Pattern) (ha : d9335 p = 1) (hb : d100986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h2 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9334 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9335 q = 1) (hb : d100986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9335, d100986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9335, d100986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43604 (p : Pattern) (ha : d9341 p = 1) (hb : d100992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d100987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43603 q ha hb
    | true =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d100988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9303 q = 1) (hb : d100954 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d100954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43599 q ha hb
    | true =>
      simp only [d9303, d100954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9304 q = 1) (hb : d100955 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d100955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d100955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9338 q = 1) (hb : d100989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9338, d100989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9338, d100989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9339 q = 1) (hb : d100990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9339, d100990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9339, d100990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9340 q = 1) (hb : d100991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9340, d100991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9340, d100991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9341 q = 1) (hb : d100992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9341, d100992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9341, d100992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43605 (p : Pattern) (ha : d100998 p = 1) (hb : d101879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d100993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43604 q ha hb
    | true =>
      simp only [d9342, d100993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100994 q = 1) (hb : d101875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100994, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d100994, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9309 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
    | true =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9310 q = 1) (hb : d100961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d100961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9310, d100961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d100995 q = 1) (hb : d101876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d100995, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100995, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d100996 q = 1) (hb : d101877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d100996, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100996, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100997 q = 1) (hb : d101878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d100997, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100997, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100998 q = 1) (hb : d101879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d100998, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100998, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43606 (p : Pattern) (ha : d101004 p = 1) (hb : d101885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100999 q = 1) (hb : d101880 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d100999, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100999, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43605 q ha hb
  have h2 (q : Pattern) (ha : d101000 q = 1) (hb : d101881 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101000, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101000, d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101001 q = 1) (hb : d101882 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101001, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101001, d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101002 q = 1) (hb : d101883 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101002, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101002, d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101003 q = 1) (hb : d101884 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101003, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101003, d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101004 q = 1) (hb : d101885 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101004, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101004, d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43607 (p : Pattern) (ha : d9436 p = 1) (hb : d101051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
    | true =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9432 q = 1) (hb : d101047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d101047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9432, d101047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9433 q = 1) (hb : d101048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d101048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9433, d101048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9434 q = 1) (hb : d101049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d101049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d101049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9435 q = 1) (hb : d101050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d101050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d101050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9436 q = 1) (hb : d101051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d101051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d101051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43608 (p : Pattern) (ha : d9394 p = 1) (hb : d101027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h2 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h5 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9393 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9394 q = 1) (hb : d101027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9394, d101027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9394, d101027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43609 (p : Pattern) (ha : d9400 p = 1) (hb : d101033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9395 q = 1) (hb : d101028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9395, d101028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43608 q ha hb
    | true =>
      simp only [d9395, d101028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9396 q = 1) (hb : d101029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9396, d101029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9396, d101029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9336 q = 1) (hb : d100987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43603 q ha hb
    | true =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9337 q = 1) (hb : d100988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9397 q = 1) (hb : d101030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9397, d101030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9397, d101030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9398 q = 1) (hb : d101031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9398, d101031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9398, d101031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9399 q = 1) (hb : d101032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9399, d101032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9399, d101032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9400 q = 1) (hb : d101033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9400, d101033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9400, d101033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43610 (p : Pattern) (ha : d9424 p = 1) (hb : d101039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d100987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43603 q ha hb
    | true =>
      simp only [d9336, d100987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d100988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d100988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9421 q = 1) (hb : d101036 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9421, d101036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9421, d101036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9422 q = 1) (hb : d101037 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9422, d101037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9422, d101037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9423 q = 1) (hb : d101038 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9423, d101038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9423, d101038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9424 q = 1) (hb : d101039 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9424, d101039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9424, d101039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43611 (p : Pattern) (ha : d101045 p = 1) (hb : d101895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9401 q = 1) (hb : d101034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9401, d101034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43609 q ha hb
    | true =>
      simp only [d9401, d101034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43604 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101035 q = 1) (hb : d101891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101035, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101035, d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9425 q = 1) (hb : d101040 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9425, d101040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43610 q ha hb
    | true =>
      simp only [d9425, d101040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9426 q = 1) (hb : d101041 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9426, d101041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9426, d101041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101042 q = 1) (hb : d101892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101042, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101042, d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101043 q = 1) (hb : d101893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101043, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101043, d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101044 q = 1) (hb : d101894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101044, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101044, d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101045 q = 1) (hb : d101895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101045, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101045, d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43612 (p : Pattern) (ha : d101057 p = 1) (hb : d101901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101046 q = 1) (hb : d101896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101046, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101046, d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43611 q ha hb
  have h2 (q : Pattern) (ha : d9437 q = 1) (hb : d101052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d101052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d101052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43607 q ha hb
  have h3 (q : Pattern) (ha : d101053 q = 1) (hb : d101897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101053, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101053, d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101054 q = 1) (hb : d101898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101054, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101054, d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101055 q = 1) (hb : d101899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101055, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101055, d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101056 q = 1) (hb : d101900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101056, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101056, d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101057 q = 1) (hb : d101901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101057, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101057, d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43613 (p : Pattern) (ha : d101063 p = 1) (hb : d101907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9321 q = 1) (hb : d100972 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9321, d100972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9321, d100972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43602 q ha hb
  have h2 (q : Pattern) (ha : d9322 q = 1) (hb : d100973 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9322, d100973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9322, d100973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9323 q = 1) (hb : d100974 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9323, d100974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9323, d100974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9324 q = 1) (hb : d100975 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9324, d100975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9324, d100975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101005 q = 1) (hb : d101886 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101005, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101005, d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43606 q ha hb
  have h6 (q : Pattern) (ha : d101006 q = 1) (hb : d101887 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101006, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101006, d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101007 q = 1) (hb : d101888 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101007, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101007, d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101008 q = 1) (hb : d101889 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101008, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101008, d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101009 q = 1) (hb : d101890 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101009, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d101009, d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101058 q = 1) (hb : d101902 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101058, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101058, d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43612 q ha hb
  have h11 (q : Pattern) (ha : d101059 q = 1) (hb : d101903 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101059, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101059, d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101060 q = 1) (hb : d101904 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101060, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101060, d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101061 q = 1) (hb : d101905 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101061, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101061, d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101062 q = 1) (hb : d101906 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101062, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101062, d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101063 q = 1) (hb : d101907 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101063, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101063, d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43614 (p : Pattern) (ha : d9497 p = 1) (hb : d101112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h2 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9496 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9497 q = 1) (hb : d101112 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9497, d101112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9497, d101112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43615 (p : Pattern) (ha : d9556 p = 1) (hb : d101123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9498 q = 1) (hb : d101113 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d101113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43614 q ha hb
    | true =>
      simp only [d9498, d101113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9499 q = 1) (hb : d101114 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d101114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d101114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9553 q = 1) (hb : d101120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9553, d101120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9553, d101120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9554 q = 1) (hb : d101121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9554, d101121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9554, d101121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9555 q = 1) (hb : d101122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9555, d101122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9555, d101122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9556 q = 1) (hb : d101123 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9556, d101123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9556, d101123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43616 (p : Pattern) (ha : d9562 p = 1) (hb : d101142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9557 q = 1) (hb : d101137 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9557, d101137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43615 q ha hb
    | true =>
      simp only [d9557, d101137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9558 q = 1) (hb : d101138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9558, d101138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9558, d101138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9559 q = 1) (hb : d101139 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9559, d101139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9559, d101139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9560 q = 1) (hb : d101140 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9560, d101140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9560, d101140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9561 q = 1) (hb : d101141 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9561, d101141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9561, d101141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9562 q = 1) (hb : d101142 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9562, d101142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9562, d101142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43617 (p : Pattern) (ha : d9484 p = 1) (hb : d101099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h2 (q : Pattern) (ha : d9476 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9477 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h5 (q : Pattern) (ha : d9480 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9481 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9482 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h9 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h12 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9483 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9484 q = 1) (hb : d101099 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9484, d101099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9484, d101099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43618 (p : Pattern) (ha : d9489 p = 1) (hb : d101104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h2 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h5 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9488 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9489 q = 1) (hb : d101104 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9489, d101104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9489, d101104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43619 (p : Pattern) (ha : d9495 p = 1) (hb : d101110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9485 q = 1) (hb : d101100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9485, d101100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43617 q ha hb
    | true =>
      simp only [d9485, d101100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9486 q = 1) (hb : d101101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9486, d101101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9486, d101101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9490 q = 1) (hb : d101105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43618 q ha hb
    | true =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9491 q = 1) (hb : d101106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9492 q = 1) (hb : d101107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9492, d101107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9492, d101107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9493 q = 1) (hb : d101108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9493, d101108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9493, d101108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9494 q = 1) (hb : d101109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9494, d101109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9494, d101109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9495 q = 1) (hb : d101110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9495, d101110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9495, d101110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43620 (p : Pattern) (ha : d9503 p = 1) (hb : d101118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d101105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43618 q ha hb
    | true =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d101106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9498 q = 1) (hb : d101113 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d101113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43614 q ha hb
    | true =>
      simp only [d9498, d101113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9499 q = 1) (hb : d101114 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d101114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d101114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9500 q = 1) (hb : d101115 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9500, d101115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9500, d101115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9501 q = 1) (hb : d101116 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9501, d101116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9501, d101116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9502 q = 1) (hb : d101117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9502, d101117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9502, d101117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9503 q = 1) (hb : d101118 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9503, d101118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9503, d101118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43621 (p : Pattern) (ha : d9545 p = 1) (hb : d101129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d101105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43618 q ha hb
    | true =>
      simp only [d9490, d101105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d101106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d101106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9542 q = 1) (hb : d101126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9542, d101126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9542, d101126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9543 q = 1) (hb : d101127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9543, d101127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9543, d101127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9544 q = 1) (hb : d101128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9544, d101128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9544, d101128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9545 q = 1) (hb : d101129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9545, d101129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9545, d101129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43622 (p : Pattern) (ha : d101135 p = 1) (hb : d101912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9504 q = 1) (hb : d101119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9504, d101119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43619 q ha hb
    | true =>
      simp only [d9504, d101119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43620 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101125 q = 1) (hb : d101908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101125, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101125, d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9546 q = 1) (hb : d101130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9546, d101130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43621 q ha hb
    | true =>
      simp only [d9546, d101130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9547 q = 1) (hb : d101131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9547, d101131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9547, d101131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101132 q = 1) (hb : d101909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101132, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101132, d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101133 q = 1) (hb : d101910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101133, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101133, d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101134 q = 1) (hb : d101911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101134, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101134, d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101135 q = 1) (hb : d101912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101135, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101135, d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43623 (p : Pattern) (ha : d101148 p = 1) (hb : d101918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101136 q = 1) (hb : d101913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101136, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101136, d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43622 q ha hb
  have h2 (q : Pattern) (ha : d9563 q = 1) (hb : d101143 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9563, d101143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9563, d101143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43616 q ha hb
  have h3 (q : Pattern) (ha : d101144 q = 1) (hb : d101914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101144, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101144, d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101145 q = 1) (hb : d101915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101145, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101145, d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101146 q = 1) (hb : d101916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101146, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101146, d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101147 q = 1) (hb : d101917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101147, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101147, d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101148 q = 1) (hb : d101918 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101148, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101148, d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43624 (p : Pattern) (ha : d101154 p = 1) (hb : d101924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101149 q = 1) (hb : d101919 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101149, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101149, d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43623 q ha hb
  have h2 (q : Pattern) (ha : d101150 q = 1) (hb : d101920 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101150, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101150, d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101151 q = 1) (hb : d101921 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101151, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101151, d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101152 q = 1) (hb : d101922 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101152, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101152, d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101153 q = 1) (hb : d101923 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101153, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101153, d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101154 q = 1) (hb : d101924 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101154, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101154, d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43625 (p : Pattern) (ha : d9642 p = 1) (hb : d101222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h2 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9641 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9642 q = 1) (hb : d101222 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9642, d101222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9642, d101222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43626 (p : Pattern) (ha : d9725 p = 1) (hb : d101233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9643 q = 1) (hb : d101223 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d101223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43625 q ha hb
    | true =>
      simp only [d9643, d101223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9644 q = 1) (hb : d101224 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d101224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d101224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9722 q = 1) (hb : d101230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9722, d101230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9722, d101230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9723 q = 1) (hb : d101231 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9723, d101231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9723, d101231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9724 q = 1) (hb : d101232 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9724, d101232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9724, d101232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9725 q = 1) (hb : d101233 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9725, d101233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9725, d101233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43627 (p : Pattern) (ha : d9731 p = 1) (hb : d101252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9726 q = 1) (hb : d101247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9726, d101247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43626 q ha hb
    | true =>
      simp only [d9726, d101247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9727 q = 1) (hb : d101248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9727, d101248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9727, d101248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9728 q = 1) (hb : d101249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9728, d101249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9728, d101249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9729 q = 1) (hb : d101250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9729, d101250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9729, d101250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9730 q = 1) (hb : d101251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9730, d101251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9730, d101251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9731 q = 1) (hb : d101252 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9731, d101252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9731, d101252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43628 (p : Pattern) (ha : d9629 p = 1) (hb : d101209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h2 (q : Pattern) (ha : d9610 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9611 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h5 (q : Pattern) (ha : d9615 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9616 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9617 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h9 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h12 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9628 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9629 q = 1) (hb : d101209 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9629, d101209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9629, d101209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43629 (p : Pattern) (ha : d9634 p = 1) (hb : d101214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h2 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h5 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9633 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9634 q = 1) (hb : d101214 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9634, d101214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9634, d101214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43630 (p : Pattern) (ha : d9640 p = 1) (hb : d101220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9630 q = 1) (hb : d101210 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9630, d101210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43628 q ha hb
    | true =>
      simp only [d9630, d101210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9631 q = 1) (hb : d101211 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9631, d101211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9631, d101211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9635 q = 1) (hb : d101215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43629 q ha hb
    | true =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9636 q = 1) (hb : d101216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9637 q = 1) (hb : d101217 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9637, d101217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9637, d101217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9638 q = 1) (hb : d101218 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9638, d101218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9638, d101218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9639 q = 1) (hb : d101219 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9639, d101219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9639, d101219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9640 q = 1) (hb : d101220 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9640, d101220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9640, d101220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43631 (p : Pattern) (ha : d9648 p = 1) (hb : d101228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d101215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43629 q ha hb
    | true =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d101216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9643 q = 1) (hb : d101223 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d101223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43625 q ha hb
    | true =>
      simp only [d9643, d101223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9644 q = 1) (hb : d101224 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d101224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d101224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9645 q = 1) (hb : d101225 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9645, d101225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9645, d101225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9646 q = 1) (hb : d101226 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9646, d101226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9646, d101226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9647 q = 1) (hb : d101227 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9647, d101227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9647, d101227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9648 q = 1) (hb : d101228 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9648, d101228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9648, d101228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43632 (p : Pattern) (ha : d9714 p = 1) (hb : d101239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d101215 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43629 q ha hb
    | true =>
      simp only [d9635, d101215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d101216 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d101216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9711 q = 1) (hb : d101236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9711, d101236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9711, d101236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9712 q = 1) (hb : d101237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9712, d101237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9712, d101237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9713 q = 1) (hb : d101238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9713, d101238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9713, d101238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9714 q = 1) (hb : d101239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9714, d101239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9714, d101239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43633 (p : Pattern) (ha : d101245 p = 1) (hb : d101930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9649 q = 1) (hb : d101229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9649, d101229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43630 q ha hb
    | true =>
      simp only [d9649, d101229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43631 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101235 q = 1) (hb : d101926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101235, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101235, d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9715 q = 1) (hb : d101240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9715, d101240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43632 q ha hb
    | true =>
      simp only [d9715, d101240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9716 q = 1) (hb : d101241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9716, d101241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9716, d101241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101242 q = 1) (hb : d101927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101242, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101242, d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101243 q = 1) (hb : d101928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101243, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101243, d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101244 q = 1) (hb : d101929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101244, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101244, d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101245 q = 1) (hb : d101930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101245, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101245, d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43634 (p : Pattern) (ha : d101258 p = 1) (hb : d101936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101246 q = 1) (hb : d101931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101246, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101246, d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43633 q ha hb
  have h2 (q : Pattern) (ha : d9732 q = 1) (hb : d101253 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9732, d101253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9732, d101253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43627 q ha hb
  have h3 (q : Pattern) (ha : d101254 q = 1) (hb : d101932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101254, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101254, d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101255 q = 1) (hb : d101933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101255, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101255, d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101256 q = 1) (hb : d101934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101256, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101256, d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101257 q = 1) (hb : d101935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101257, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101257, d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101258 q = 1) (hb : d101936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101258, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101258, d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43635 (p : Pattern) (ha : d101264 p = 1) (hb : d101942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101259 q = 1) (hb : d101937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101259, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101259, d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43634 q ha hb
  have h2 (q : Pattern) (ha : d101260 q = 1) (hb : d101938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101260, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101260, d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101261 q = 1) (hb : d101939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101261, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101261, d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101262 q = 1) (hb : d101940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101262, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101262, d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101263 q = 1) (hb : d101941 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101263, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101263, d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101264 q = 1) (hb : d101942 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101264, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101264, d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43636 (p : Pattern) (ha : d9875 p = 1) (hb : d101396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h2 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9874 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9875 q = 1) (hb : d101396 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9875, d101396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9875, d101396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43637 (p : Pattern) (ha : d10010 p = 1) (hb : d101415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9876 q = 1) (hb : d101397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43636 q ha hb
    | true =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9877 q = 1) (hb : d101398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10007 q = 1) (hb : d101412 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10007, d101412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10007, d101412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10008 q = 1) (hb : d101413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10008, d101413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10008, d101413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10009 q = 1) (hb : d101414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10009, d101414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10009, d101414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10010 q = 1) (hb : d101415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10010, d101415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10010, d101415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43638 (p : Pattern) (ha : d10016 p = 1) (hb : d101443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10011 q = 1) (hb : d101438 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10011, d101438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43637 q ha hb
    | true =>
      simp only [d10011, d101438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10012 q = 1) (hb : d101439 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10012, d101439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10012, d101439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10013 q = 1) (hb : d101440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10013, d101440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10013, d101440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10014 q = 1) (hb : d101441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10014, d101441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10014, d101441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10015 q = 1) (hb : d101442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10015, d101442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10015, d101442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10016 q = 1) (hb : d101443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10016, d101443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10016, d101443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43639 (p : Pattern) (ha : d9856 p = 1) (hb : d101377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h2 (q : Pattern) (ha : d9808 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9809 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h5 (q : Pattern) (ha : d9823 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9824 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9825 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h9 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h12 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9855 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9856 q = 1) (hb : d101377 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9856, d101377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9856, d101377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43640 (p : Pattern) (ha : d9861 p = 1) (hb : d101382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9859 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9860 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9861 q = 1) (hb : d101382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9861, d101382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9861, d101382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43641 (p : Pattern) (ha : d9867 p = 1) (hb : d101388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9857 q = 1) (hb : d101378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9857, d101378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43639 q ha hb
    | true =>
      simp only [d9857, d101378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9858 q = 1) (hb : d101379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9858, d101379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9858, d101379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9862 q = 1) (hb : d101383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d101383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43640 q ha hb
    | true =>
      simp only [d9862, d101383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9863 q = 1) (hb : d101384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d101384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d101384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9864 q = 1) (hb : d101385 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9864, d101385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9864, d101385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9865 q = 1) (hb : d101386 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9865, d101386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9865, d101386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9866 q = 1) (hb : d101387 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9866, d101387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9866, d101387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9867 q = 1) (hb : d101388 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9867, d101388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9867, d101388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43642 (p : Pattern) (ha : d9881 p = 1) (hb : d101402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9862 q = 1) (hb : d101383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d101383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43640 q ha hb
    | true =>
      simp only [d9862, d101383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9863 q = 1) (hb : d101384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d101384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d101384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d101397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43636 q ha hb
    | true =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d101398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9878 q = 1) (hb : d101399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9878, d101399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9878, d101399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9879 q = 1) (hb : d101400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9879, d101400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9879, d101400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9880 q = 1) (hb : d101401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9880, d101401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9880, d101401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9881 q = 1) (hb : d101402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9881, d101402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9881, d101402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43643 (p : Pattern) (ha : d9993 p = 1) (hb : d101424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h9 (q : Pattern) (ha : d9989 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9990 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9991 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9992 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9993 q = 1) (hb : d101424 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9993, d101424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9993, d101424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43644 (p : Pattern) (ha : d9999 p = 1) (hb : d101430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9994 q = 1) (hb : d101425 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9994, d101425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43643 q ha hb
    | true =>
      simp only [d9994, d101425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9995 q = 1) (hb : d101426 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9995, d101426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9995, d101426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9996 q = 1) (hb : d101427 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9996, d101427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9996, d101427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9997 q = 1) (hb : d101428 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9997, d101428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9997, d101428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9998 q = 1) (hb : d101429 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9998, d101429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9998, d101429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9999 q = 1) (hb : d101430 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9999, d101430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9999, d101430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43645 (p : Pattern) (ha : d101436 p = 1) (hb : d101949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9882 q = 1) (hb : d101403 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9882, d101403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43641 q ha hb
    | true =>
      simp only [d9882, d101403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43642 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101417 q = 1) (hb : d101945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101417, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101417, d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10000 q = 1) (hb : d101431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10000, d101431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43644 q ha hb
    | true =>
      simp only [d10000, d101431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10001 q = 1) (hb : d101432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10001, d101432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10001, d101432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101433 q = 1) (hb : d101946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101433, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101433, d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101434 q = 1) (hb : d101947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101434, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101434, d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101435 q = 1) (hb : d101948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101435, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101435, d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101436 q = 1) (hb : d101949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101436, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101436, d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43646 (p : Pattern) (ha : d101449 p = 1) (hb : d101955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101437 q = 1) (hb : d101950 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101437, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101437, d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43645 q ha hb
  have h2 (q : Pattern) (ha : d10017 q = 1) (hb : d101444 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10017, d101444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10017, d101444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43638 q ha hb
  have h3 (q : Pattern) (ha : d101445 q = 1) (hb : d101951 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101445, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101445, d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101446 q = 1) (hb : d101952 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101446, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101446, d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101447 q = 1) (hb : d101953 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101447, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101447, d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101448 q = 1) (hb : d101954 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101448, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101448, d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101449 q = 1) (hb : d101955 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101449, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101449, d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43647 (p : Pattern) (ha : d101455 p = 1) (hb : d101961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101450 q = 1) (hb : d101956 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101450, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101450, d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43646 q ha hb
  have h2 (q : Pattern) (ha : d101451 q = 1) (hb : d101957 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101451, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101451, d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101452 q = 1) (hb : d101958 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101452, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101452, d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101453 q = 1) (hb : d101959 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101453, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101453, d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101454 q = 1) (hb : d101960 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101454, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101454, d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101455 q = 1) (hb : d101961 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101455, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101455, d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43648 (p : Pattern) (ha : d10169 p = 1) (hb : d101596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h2 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10168 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10169 q = 1) (hb : d101596 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10169, d101596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10169, d101596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43649 (p : Pattern) (ha : d10316 p = 1) (hb : d101615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10170 q = 1) (hb : d101597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43648 q ha hb
    | true =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10171 q = 1) (hb : d101598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10313 q = 1) (hb : d101612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10313, d101612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10313, d101612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10314 q = 1) (hb : d101613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10314, d101613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10314, d101613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10315 q = 1) (hb : d101614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10315, d101614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10315, d101614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10316 q = 1) (hb : d101615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10316, d101615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10316, d101615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43650 (p : Pattern) (ha : d10322 p = 1) (hb : d101643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10317 q = 1) (hb : d101638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10317, d101638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43649 q ha hb
    | true =>
      simp only [d10317, d101638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10318 q = 1) (hb : d101639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10318, d101639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10318, d101639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10319 q = 1) (hb : d101640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10319, d101640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10319, d101640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10320 q = 1) (hb : d101641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10320, d101641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10320, d101641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10321 q = 1) (hb : d101642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10321, d101642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10321, d101642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10322 q = 1) (hb : d101643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10322, d101643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10322, d101643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43651 (p : Pattern) (ha : d10147 p = 1) (hb : d101574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h2 (q : Pattern) (ha : d10093 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10094 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h5 (q : Pattern) (ha : d10108 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10109 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10110 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h9 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h12 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10146 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10147 q = 1) (hb : d101574 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10147, d101574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10147, d101574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43652 (p : Pattern) (ha : d10152 p = 1) (hb : d101579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10150 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10151 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10152 q = 1) (hb : d101579 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10152, d101579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10152, d101579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43653 (p : Pattern) (ha : d10158 p = 1) (hb : d101585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10148 q = 1) (hb : d101575 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10148, d101575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43651 q ha hb
    | true =>
      simp only [d10148, d101575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10149 q = 1) (hb : d101576 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10149, d101576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10149, d101576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10153 q = 1) (hb : d101580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d101580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43652 q ha hb
    | true =>
      simp only [d10153, d101580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10154 q = 1) (hb : d101581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d101581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d101581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10155 q = 1) (hb : d101582 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10155, d101582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10155, d101582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10156 q = 1) (hb : d101583 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10156, d101583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10156, d101583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10157 q = 1) (hb : d101584 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10157, d101584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10157, d101584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10158 q = 1) (hb : d101585 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10158, d101585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10158, d101585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43654 (p : Pattern) (ha : d10175 p = 1) (hb : d101602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10153 q = 1) (hb : d101580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d101580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43652 q ha hb
    | true =>
      simp only [d10153, d101580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10154 q = 1) (hb : d101581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d101581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d101581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d101597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43648 q ha hb
    | true =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d101598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10172 q = 1) (hb : d101599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10172, d101599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10172, d101599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10173 q = 1) (hb : d101600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10173, d101600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10173, d101600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10174 q = 1) (hb : d101601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10174, d101601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10174, d101601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10175 q = 1) (hb : d101602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10175, d101602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10175, d101602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43655 (p : Pattern) (ha : d10299 p = 1) (hb : d101624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h9 (q : Pattern) (ha : d10295 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10296 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10297 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10298 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10299 q = 1) (hb : d101624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10299, d101624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10299, d101624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43656 (p : Pattern) (ha : d10305 p = 1) (hb : d101630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10300 q = 1) (hb : d101625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10300, d101625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43655 q ha hb
    | true =>
      simp only [d10300, d101625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10301 q = 1) (hb : d101626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10301, d101626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10301, d101626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10302 q = 1) (hb : d101627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10302, d101627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10302, d101627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10303 q = 1) (hb : d101628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10303, d101628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10303, d101628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10304 q = 1) (hb : d101629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10304, d101629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10304, d101629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10305 q = 1) (hb : d101630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10305, d101630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10305, d101630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43657 (p : Pattern) (ha : d101636 p = 1) (hb : d101969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10176 q = 1) (hb : d101603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10176, d101603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43653 q ha hb
    | true =>
      simp only [d10176, d101603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43654 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101617 q = 1) (hb : d101965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101617, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101617, d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10306 q = 1) (hb : d101631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10306, d101631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43656 q ha hb
    | true =>
      simp only [d10306, d101631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10307 q = 1) (hb : d101632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10307, d101632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10307, d101632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101633 q = 1) (hb : d101966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101633, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101633, d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101634 q = 1) (hb : d101967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101634, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101634, d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101635 q = 1) (hb : d101968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101635, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101635, d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101636 q = 1) (hb : d101969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101636, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101636, d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43658 (p : Pattern) (ha : d101649 p = 1) (hb : d101975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101637 q = 1) (hb : d101970 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101637, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101637, d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43657 q ha hb
  have h2 (q : Pattern) (ha : d10323 q = 1) (hb : d101644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10323, d101644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10323, d101644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43650 q ha hb
  have h3 (q : Pattern) (ha : d101645 q = 1) (hb : d101971 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101645, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101645, d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101646 q = 1) (hb : d101972 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101646, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101646, d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101647 q = 1) (hb : d101973 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101647, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101647, d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101648 q = 1) (hb : d101974 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101648, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101648, d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101649 q = 1) (hb : d101975 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101649, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101649, d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43659 (p : Pattern) (ha : d101655 p = 1) (hb : d101981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101650 q = 1) (hb : d101976 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101650, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101650, d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43658 q ha hb
  have h2 (q : Pattern) (ha : d101651 q = 1) (hb : d101977 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101651, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101651, d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101652 q = 1) (hb : d101978 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101652, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101652, d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101653 q = 1) (hb : d101979 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101653, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101653, d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101654 q = 1) (hb : d101980 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101654, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101654, d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101655 q = 1) (hb : d101981 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101655, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101655, d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43660 (p : Pattern) (ha : d10446 p = 1) (hb : d101767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h2 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10445 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10446 q = 1) (hb : d101767 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10446, d101767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10446, d101767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43661 (p : Pattern) (ha : d10582 p = 1) (hb : d101786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10447 q = 1) (hb : d101768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43660 q ha hb
    | true =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10448 q = 1) (hb : d101769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10579 q = 1) (hb : d101783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10579, d101783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10579, d101783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10580 q = 1) (hb : d101784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10580, d101784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10580, d101784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10581 q = 1) (hb : d101785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10581, d101785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10581, d101785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10582 q = 1) (hb : d101786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10582, d101786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10582, d101786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43662 (p : Pattern) (ha : d10588 p = 1) (hb : d101814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10583 q = 1) (hb : d101809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10583, d101809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43661 q ha hb
    | true =>
      simp only [d10583, d101809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10584 q = 1) (hb : d101810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10584, d101810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10584, d101810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10585 q = 1) (hb : d101811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10585, d101811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10585, d101811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10586 q = 1) (hb : d101812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10586, d101812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10586, d101812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10587 q = 1) (hb : d101813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10587, d101813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10587, d101813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10588 q = 1) (hb : d101814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10588, d101814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10588, d101814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43663 (p : Pattern) (ha : d10424 p = 1) (hb : d101745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h2 (q : Pattern) (ha : d10379 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10380 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h5 (q : Pattern) (ha : d10384 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10385 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10386 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h9 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h12 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10423 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10424 q = 1) (hb : d101745 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10424, d101745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10424, d101745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43664 (p : Pattern) (ha : d10429 p = 1) (hb : d101750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10427 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10428 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10429 q = 1) (hb : d101750 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10429, d101750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10429, d101750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro43665 (p : Pattern) (ha : d10435 p = 1) (hb : d101756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10425 q = 1) (hb : d101746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10425, d101746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43663 q ha hb
    | true =>
      simp only [d10425, d101746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10426 q = 1) (hb : d101747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10426, d101747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10426, d101747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10430 q = 1) (hb : d101751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d101751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43664 q ha hb
    | true =>
      simp only [d10430, d101751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10431 q = 1) (hb : d101752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d101752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d101752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10432 q = 1) (hb : d101753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10432, d101753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10432, d101753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10433 q = 1) (hb : d101754 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10433, d101754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10433, d101754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10434 q = 1) (hb : d101755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10434, d101755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10434, d101755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10435 q = 1) (hb : d101756 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10435, d101756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10435, d101756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43666 (p : Pattern) (ha : d10452 p = 1) (hb : d101773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10430 q = 1) (hb : d101751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d101751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43664 q ha hb
    | true =>
      simp only [d10430, d101751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10431 q = 1) (hb : d101752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d101752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d101752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d101768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43660 q ha hb
    | true =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d101769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10449 q = 1) (hb : d101770 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10449, d101770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10449, d101770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10450 q = 1) (hb : d101771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10450, d101771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10450, d101771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10451 q = 1) (hb : d101772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10451, d101772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10451, d101772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10452 q = 1) (hb : d101773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10452, d101773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10452, d101773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43667 (p : Pattern) (ha : d10565 p = 1) (hb : d101795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h9 (q : Pattern) (ha : d10561 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10562 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10563 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10564 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10565 q = 1) (hb : d101795 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10565, d101795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10565, d101795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43668 (p : Pattern) (ha : d10571 p = 1) (hb : d101801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10566 q = 1) (hb : d101796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10566, d101796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43667 q ha hb
    | true =>
      simp only [d10566, d101796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10567 q = 1) (hb : d101797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10567, d101797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10567, d101797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10568 q = 1) (hb : d101798 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10568, d101798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10568, d101798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10569 q = 1) (hb : d101799 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10569, d101799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10569, d101799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10570 q = 1) (hb : d101800 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10570, d101800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10570, d101800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10571 q = 1) (hb : d101801 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10571, d101801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10571, d101801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43669 (p : Pattern) (ha : d101807 p = 1) (hb : d101990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10453 q = 1) (hb : d101774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10453, d101774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43665 q ha hb
    | true =>
      simp only [d10453, d101774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43666 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101787 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101788 q = 1) (hb : d101986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101788, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101788, d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10572 q = 1) (hb : d101802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10572, d101802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43668 q ha hb
    | true =>
      simp only [d10572, d101802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10573 q = 1) (hb : d101803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10573, d101803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10573, d101803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101804 q = 1) (hb : d101987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101804, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101804, d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d101805 q = 1) (hb : d101988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101805, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101805, d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101806 q = 1) (hb : d101989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101806, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101806, d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101807 q = 1) (hb : d101990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101807, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101807, d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43670 (p : Pattern) (ha : d101820 p = 1) (hb : d101996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101808 q = 1) (hb : d101991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101808, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101808, d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43669 q ha hb
  have h2 (q : Pattern) (ha : d10589 q = 1) (hb : d101815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10589, d101815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10589, d101815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43662 q ha hb
  have h3 (q : Pattern) (ha : d101816 q = 1) (hb : d101992 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101816, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101816, d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101817 q = 1) (hb : d101993 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101817, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101817, d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101818 q = 1) (hb : d101994 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101818, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101818, d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101819 q = 1) (hb : d101995 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101819, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101819, d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101820 q = 1) (hb : d101996 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101820, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101820, d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43671 (p : Pattern) (ha : d101826 p = 1) (hb : d102002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101821 q = 1) (hb : d101997 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101821, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101821, d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43670 q ha hb
  have h2 (q : Pattern) (ha : d101822 q = 1) (hb : d101998 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101822, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101822, d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101823 q = 1) (hb : d101999 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101823, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101823, d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101824 q = 1) (hb : d102000 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101824, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101824, d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101825 q = 1) (hb : d102001 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101825, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101825, d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101826 q = 1) (hb : d102002 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101826, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101826, d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43672 (p : Pattern) (ha : d101832 p = 1) (hb : d102008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101155 q = 1) (hb : d101925 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101155, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43613 q ha hb
    | true =>
      simp only [d101155, d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43624 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101265 q = 1) (hb : d101943 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101265, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101265, d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43635 q ha hb
  have h3 (q : Pattern) (ha : d101266 q = 1) (hb : d101944 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101266, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101266, d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101456 q = 1) (hb : d101962 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101456, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101456, d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43647 q ha hb
  have h5 (q : Pattern) (ha : d101457 q = 1) (hb : d101963 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101457, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101457, d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101458 q = 1) (hb : d101964 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101458, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101458, d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101656 q = 1) (hb : d101982 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101656, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101656, d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43659 q ha hb
  have h8 (q : Pattern) (ha : d101657 q = 1) (hb : d101983 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101657, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101657, d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101658 q = 1) (hb : d101984 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101658, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101658, d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101659 q = 1) (hb : d101985 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101659, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101659, d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101827 q = 1) (hb : d102003 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101827, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101827, d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43671 q ha hb
  have h12 (q : Pattern) (ha : d101828 q = 1) (hb : d102004 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101828, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101828, d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101829 q = 1) (hb : d102005 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101829, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101829, d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101830 q = 1) (hb : d102006 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101830, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101830, d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101831 q = 1) (hb : d102007 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d101831, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d101831, d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101832 q = 1) (hb : d102008 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d101832, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d101832, d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43673 (p : Pattern) (ha : d101838 p = 1) (hb : d102014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101833 q = 1) (hb : d102009 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d101833, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43672 q ha hb
    | true =>
      simp only [d101833, d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101834 q = 1) (hb : d102010 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d101834, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101834, d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101835 q = 1) (hb : d102011 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d101835, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101835, d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101836 q = 1) (hb : d102012 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d101836, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101836, d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101837 q = 1) (hb : d102013 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d101837, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101837, d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101838 q = 1) (hb : d102014 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d101838, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101838, d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43674 (p : Pattern) (ha : d101844 p = 1) (hb : d102020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101839 q = 1) (hb : d102015 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d101839, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43673 q ha hb
    | true =>
      simp only [d101839, d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101840 q = 1) (hb : d102016 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d101840, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101840, d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101841 q = 1) (hb : d102017 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d101841, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101841, d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101842 q = 1) (hb : d102018 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d101842, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101842, d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101843 q = 1) (hb : d102019 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d101843, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101843, d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101844 q = 1) (hb : d102020 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d101844, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101844, d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43675 (p : Pattern) (ha : d101850 p = 1) (hb : d102026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101845 q = 1) (hb : d102021 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d101845, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43674 q ha hb
    | true =>
      simp only [d101845, d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101846 q = 1) (hb : d102022 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d101846, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101846, d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101847 q = 1) (hb : d102023 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d101847, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101847, d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101848 q = 1) (hb : d102024 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d101848, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101848, d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101849 q = 1) (hb : d102025 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d101849, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101849, d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101850 q = 1) (hb : d102026 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d101850, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101850, d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43676 (p : Pattern) (ha : d101856 p = 1) (hb : d102032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101851 q = 1) (hb : d102027 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d101851, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43675 q ha hb
    | true =>
      simp only [d101851, d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101852 q = 1) (hb : d102028 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d101852, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101852, d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101853 q = 1) (hb : d102029 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d101853, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101853, d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101854 q = 1) (hb : d102030 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d101854, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101854, d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101855 q = 1) (hb : d102031 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d101855, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101855, d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101856 q = 1) (hb : d102032 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d101856, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101856, d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43677 (p : Pattern) (ha : d101862 p = 1) (hb : d102038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101857 q = 1) (hb : d102033 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d101857, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43676 q ha hb
    | true =>
      simp only [d101857, d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101858 q = 1) (hb : d102034 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d101858, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101858, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101859 q = 1) (hb : d102035 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d101859, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101859, d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101860 q = 1) (hb : d102036 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d101860, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101860, d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101861 q = 1) (hb : d102037 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d101861, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101861, d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101862 q = 1) (hb : d102038 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d101862, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101862, d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43678 (p : Pattern) (ha : d101868 p = 1) (hb : d102044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101863 q = 1) (hb : d102039 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d101863, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43677 q ha hb
    | true =>
      simp only [d101863, d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101864 q = 1) (hb : d102040 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d101864, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101864, d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101865 q = 1) (hb : d102041 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d101865, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101865, d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101866 q = 1) (hb : d102042 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d101866, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101866, d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101867 q = 1) (hb : d102043 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d101867, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101867, d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101868 q = 1) (hb : d102044 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d101868, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101868, d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43679 (p : Pattern) (ha : d101874 p = 1) (hb : d102050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101869 q = 1) (hb : d102045 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d101869, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43678 q ha hb
    | true =>
      simp only [d101869, d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101870 q = 1) (hb : d102046 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d101870, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101870, d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101871 q = 1) (hb : d102047 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d101871, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101871, d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101872 q = 1) (hb : d102048 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d101872, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101872, d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101873 q = 1) (hb : d102049 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d101873, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101873, d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101874 q = 1) (hb : d102050 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d101874, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101874, d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43680 (p : Pattern) (ha : d129672 p = 1) (hb : d188529 p = 1) : d129477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d129672 q = 1) : d9437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43526 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188525 q = 1) : d129473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188525, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188525, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188526 q = 1) : d129474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188526, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188526, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188527 q = 1) : d129475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188527, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188527, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188528 q = 1) : d129476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188528, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188528, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188529 q = 1) : d129477 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188529, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188529, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43681 (p : Pattern) (ha : d129672 p = 1) (hb : d188539 p = 1) : d129487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d129672 q = 1) : d9342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43523 q ha hb
    | true =>
      simp only [d19776, d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43519 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188535 q = 1) : d129483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188535, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188535, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188536 q = 1) : d129484 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188536, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188536, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188537 q = 1) : d129485 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188537, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188537, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188538 q = 1) : d129486 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188538, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188538, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188539 q = 1) : d129487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188539, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188539, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43682 (p : Pattern) (ha : d129672 p = 1) (hb : d188545 p = 1) : d129493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188540 q = 1) : d129488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188540, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188540, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43681 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188541 q = 1) : d129489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188541, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188541, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188542 q = 1) : d129490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188542, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188542, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188543 q = 1) : d129491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188543, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188543, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188544 q = 1) : d129492 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188544, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188544, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188545 q = 1) : d129493 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188545, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188545, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43683 (p : Pattern) (ha : d129672 p = 1) (hb : d188551 p = 1) : d129499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188530 q = 1) : d129478 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188530, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188530, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43680 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188531 q = 1) : d129479 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188531, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188531, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188532 q = 1) : d129480 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188532, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188532, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188533 q = 1) : d129481 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188533, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188533, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188534 q = 1) : d129482 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188534, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188534, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188546 q = 1) : d129494 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188546, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188546, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43682 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d188547 q = 1) : d129495 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188547, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188547, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d188548 q = 1) : d129496 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188548, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188548, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d188549 q = 1) : d129497 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188549, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188549, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d188550 q = 1) : d129498 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188550, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188550, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d188551 q = 1) : d129499 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188551, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188551, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43684 (p : Pattern) (ha : d129672 p = 1) (hb : d188557 p = 1) : d129505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188552 q = 1) : d129500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188552, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43539 q hb ha
    | true =>
      simp only [d188552, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43534 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188553 q = 1) : d129501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188553, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188553, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188554 q = 1) : d129502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188554, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188554, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188555 q = 1) : d129503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188555, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188555, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188556 q = 1) : d129504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188556, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188556, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188557 q = 1) : d129505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188557, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188557, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43685 (p : Pattern) (ha : d129672 p = 1) (hb : d188563 p = 1) : d129511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188558 q = 1) : d129506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188558, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188558, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43684 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188559 q = 1) : d129507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188559, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188559, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188560 q = 1) : d129508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188560, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188560, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188561 q = 1) : d129509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188561, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188561, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188562 q = 1) : d129510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188562, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188562, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188563 q = 1) : d129511 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188563, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188563, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43686 (p : Pattern) (ha : d129672 p = 1) (hb : d188569 p = 1) : d129517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188564 q = 1) : d129512 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188564, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188564, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43685 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188565 q = 1) : d129513 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188565, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188565, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188566 q = 1) : d129514 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188566, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188566, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188567 q = 1) : d129515 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188567, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188567, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188568 q = 1) : d129516 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188568, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188568, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188569 q = 1) : d129517 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188569, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188569, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43687 (p : Pattern) (ha : d129672 p = 1) (hb : d188576 p = 1) : d129524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188571 q = 1) : d129519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188571, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43550 q hb ha
    | true =>
      simp only [d188571, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43545 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188572 q = 1) : d129520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188572, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188572, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188573 q = 1) : d129521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188573, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188573, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188574 q = 1) : d129522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188574, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188574, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188575 q = 1) : d129523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188575, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188575, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188576 q = 1) : d129524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188576, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188576, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43688 (p : Pattern) (ha : d129672 p = 1) (hb : d188582 p = 1) : d129530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188577 q = 1) : d129525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188577, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188577, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43687 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188578 q = 1) : d129526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188578, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188578, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188579 q = 1) : d129527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188579, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188579, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188580 q = 1) : d129528 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188580, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188580, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188581 q = 1) : d129529 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188581, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188581, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188582 q = 1) : d129530 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188582, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188582, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43689 (p : Pattern) (ha : d129672 p = 1) (hb : d188588 p = 1) : d129536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188583 q = 1) : d129531 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188583, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188583, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43688 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188584 q = 1) : d129532 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188584, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188584, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188585 q = 1) : d129533 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188585, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188585, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188586 q = 1) : d129534 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188586, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188586, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188587 q = 1) : d129535 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188587, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188587, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188588 q = 1) : d129536 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188588, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188588, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43690 (p : Pattern) (ha : d129672 p = 1) (hb : d188592 p = 1) : d129540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9851 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20039 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20039, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20040 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20041 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9870 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20055 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20055, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20056 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20057 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d188591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129539 q = 1) (hb : d129672 q = 1) : d129539 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d188592 q = 1) : d129540 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d188592, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d188592, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro43691 (p : Pattern) (ha : d129672 p = 1) (hb : d188598 p = 1) : d129546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188593 q = 1) : d129541 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188593, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43690 q ha hb
    | true =>
      simp only [d188593, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188594 q = 1) : d129542 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188594, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188594, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d129672 q = 1) : d9876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43555 q ha hb
    | true =>
      simp only [d20060, d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d129672 q = 1) : d9877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188595 q = 1) : d129543 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188595, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188595, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188596 q = 1) : d129544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188596, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188596, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d188597 q = 1) : d129545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188597, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188597, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d188598 q = 1) : d129546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188598, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188598, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43692 (p : Pattern) (ha : d129672 p = 1) (hb : d188604 p = 1) : d129552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188599 q = 1) : d129547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188599, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43691 q ha hb
    | true =>
      simp only [d188599, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43556 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188600 q = 1) : d129548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188600, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188600, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188601 q = 1) : d129549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188601, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188601, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188602 q = 1) : d129550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188602, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188602, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188603 q = 1) : d129551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188603, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188603, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188604 q = 1) : d129552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188604, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188604, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43693 (p : Pattern) (ha : d129672 p = 1) (hb : d188610 p = 1) : d129558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188605 q = 1) : d129553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188605, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188605, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43692 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188606 q = 1) : d129554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188606, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188606, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188607 q = 1) : d129555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188607, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188607, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188608 q = 1) : d129556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188608, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188608, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188609 q = 1) : d129557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188609, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188609, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188610 q = 1) : d129558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188610, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188610, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43694 (p : Pattern) (ha : d129672 p = 1) (hb : d188616 p = 1) : d129564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188611 q = 1) : d129559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188611, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188611, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43693 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188612 q = 1) : d129560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188612, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188612, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188613 q = 1) : d129561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188613, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188613, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188614 q = 1) : d129562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188614, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188614, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188615 q = 1) : d129563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188615, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188615, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188616 q = 1) : d129564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188616, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188616, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43695 (p : Pattern) (ha : d129672 p = 1) (hb : d188621 p = 1) : d129569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10142 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20143 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20143, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20144 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20145 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10164 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20159 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20159, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20160 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20161 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d188620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129568 q = 1) (hb : d129672 q = 1) : d129568 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d188621 q = 1) : d129569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d188621, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d188621, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro43696 (p : Pattern) (ha : d129672 p = 1) (hb : d188627 p = 1) : d129575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188622 q = 1) : d129570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188622, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43695 q ha hb
    | true =>
      simp only [d188622, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188623 q = 1) : d129571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188623, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188623, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d129672 q = 1) : d10170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43567 q ha hb
    | true =>
      simp only [d20164, d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d129672 q = 1) : d10171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188624 q = 1) : d129572 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188624, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188624, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188625 q = 1) : d129573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188625, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188625, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d188626 q = 1) : d129574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188626, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188626, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d188627 q = 1) : d129575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188627, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188627, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43697 (p : Pattern) (ha : d129672 p = 1) (hb : d188633 p = 1) : d129581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188628 q = 1) : d129576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188628, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43696 q ha hb
    | true =>
      simp only [d188628, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43568 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188629 q = 1) : d129577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188629, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188629, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188630 q = 1) : d129578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188630, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188630, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188631 q = 1) : d129579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188631, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188631, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188632 q = 1) : d129580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188632, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188632, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188633 q = 1) : d129581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188633, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188633, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43698 (p : Pattern) (ha : d129672 p = 1) (hb : d188639 p = 1) : d129587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188634 q = 1) : d129582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188634, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188634, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43697 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188635 q = 1) : d129583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188635, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188635, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188636 q = 1) : d129584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188636, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188636, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188637 q = 1) : d129585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188637, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188637, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188638 q = 1) : d129586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188638, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188638, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188639 q = 1) : d129587 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188639, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188639, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43699 (p : Pattern) (ha : d129672 p = 1) (hb : d188645 p = 1) : d129593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188640 q = 1) : d129588 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188640, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188640, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43698 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188641 q = 1) : d129589 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188641, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188641, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188642 q = 1) : d129590 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188642, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188642, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188643 q = 1) : d129591 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188643, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188643, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188644 q = 1) : d129592 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188644, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188644, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188645 q = 1) : d129593 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188645, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188645, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43700 (p : Pattern) (ha : d129672 p = 1) (hb : d188651 p = 1) : d129599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20248 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20248, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20249 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20250 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20264 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20264, d129672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d20265 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20266 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d188650 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129598 q = 1) (hb : d129672 q = 1) : d129598 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d188651 q = 1) : d129599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d188651, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d188651, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro43701 (p : Pattern) (ha : d129672 p = 1) (hb : d188657 p = 1) : d129605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188652 q = 1) : d129600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188652, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43700 q ha hb
    | true =>
      simp only [d188652, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188653 q = 1) : d129601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188653, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188653, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d129672 q = 1) : d10447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43579 q ha hb
    | true =>
      simp only [d20269, d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d129672 q = 1) : d10448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188654 q = 1) : d129602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188654, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188654, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188655 q = 1) : d129603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188655, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188655, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d188656 q = 1) : d129604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188656, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188656, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d188657 q = 1) : d129605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188657, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188657, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43702 (p : Pattern) (ha : d129672 p = 1) (hb : d188663 p = 1) : d129611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188658 q = 1) : d129606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188658, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43701 q ha hb
    | true =>
      simp only [d188658, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43580 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188659 q = 1) : d129607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188659, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188659, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188660 q = 1) : d129608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188660, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188660, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188661 q = 1) : d129609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188661, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188661, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188662 q = 1) : d129610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188662, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188662, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188663 q = 1) : d129611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188663, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188663, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43703 (p : Pattern) (ha : d129672 p = 1) (hb : d188669 p = 1) : d129617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188664 q = 1) : d129612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188664, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188664, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43702 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188665 q = 1) : d129613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188665, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188665, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188666 q = 1) : d129614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188666, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188666, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188667 q = 1) : d129615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188667, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188667, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188668 q = 1) : d129616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188668, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188668, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188669 q = 1) : d129617 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188669, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188669, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43704 (p : Pattern) (ha : d129672 p = 1) (hb : d188675 p = 1) : d129623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188670 q = 1) : d129618 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188670, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188670, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43703 q ha hb
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188671 q = 1) : d129619 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188671, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188671, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188672 q = 1) : d129620 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188672, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188672, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188673 q = 1) : d129621 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188673, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188673, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188674 q = 1) : d129622 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188674, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188674, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188675 q = 1) : d129623 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188675, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188675, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43705 (p : Pattern) (ha : d129672 p = 1) (hb : d188681 p = 1) : d129629 p = 1 := by
  have h0 (q : Pattern) (ha : d129672 q = 1) (hb : d188570 q = 1) : d129518 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188570, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43683 q ha hb
    | true =>
      simp only [d188570, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43686 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188589 q = 1) : d129537 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188589, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188589, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43689 q ha hb
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188590 q = 1) : d129538 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188590, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d188590, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188617 q = 1) : d129565 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188617, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188617, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43694 q ha hb
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188618 q = 1) : d129566 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188618, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188618, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188619 q = 1) : d129567 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188619, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188619, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129672 q = 1) (hb : d188646 q = 1) : d129594 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188646, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188646, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43699 q ha hb
  have h8 (q : Pattern) (ha : d129672 q = 1) (hb : d188647 q = 1) : d129595 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188647, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188647, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129672 q = 1) (hb : d188648 q = 1) : d129596 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188648, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188648, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129672 q = 1) (hb : d188649 q = 1) : d129597 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d188649, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188649, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129672 q = 1) (hb : d188676 q = 1) : d129624 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188676, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188676, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43704 q ha hb
  have h12 (q : Pattern) (ha : d129672 q = 1) (hb : d188677 q = 1) : d129625 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188677, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188677, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129672 q = 1) (hb : d188678 q = 1) : d129626 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188678, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188678, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129672 q = 1) (hb : d188679 q = 1) : d129627 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d188679, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188679, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129672 q = 1) (hb : d188680 q = 1) : d129628 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d188680, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d188680, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129672 q = 1) (hb : d188681 q = 1) : d129629 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d188681, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d188681, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43706 (p : Pattern) (ha : d129672 p = 1) (hb : d188687 p = 1) : d129635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188682 q = 1) : d129630 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d188682, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43705 q ha hb
    | true =>
      simp only [d188682, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188683 q = 1) : d129631 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d188683, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188683, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188684 q = 1) : d129632 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d188684, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188684, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188685 q = 1) : d129633 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d188685, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188685, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188686 q = 1) : d129634 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d188686, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188686, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188687 q = 1) : d129635 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d188687, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188687, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43707 (p : Pattern) (ha : d129672 p = 1) (hb : d188693 p = 1) : d129641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188688 q = 1) : d129636 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d188688, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43706 q ha hb
    | true =>
      simp only [d188688, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188689 q = 1) : d129637 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d188689, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188689, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188690 q = 1) : d129638 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d188690, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188690, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188691 q = 1) : d129639 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d188691, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188691, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188692 q = 1) : d129640 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d188692, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188692, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188693 q = 1) : d129641 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d188693, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188693, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43708 (p : Pattern) (ha : d129672 p = 1) (hb : d188699 p = 1) : d129647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188694 q = 1) : d129642 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d188694, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43707 q ha hb
    | true =>
      simp only [d188694, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188695 q = 1) : d129643 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d188695, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188695, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188696 q = 1) : d129644 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d188696, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188696, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188697 q = 1) : d129645 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d188697, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188697, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188698 q = 1) : d129646 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d188698, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188698, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188699 q = 1) : d129647 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d188699, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188699, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43709 (p : Pattern) (ha : d129672 p = 1) (hb : d188705 p = 1) : d129653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188700 q = 1) : d129648 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d188700, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43708 q ha hb
    | true =>
      simp only [d188700, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188701 q = 1) : d129649 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d188701, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188701, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188702 q = 1) : d129650 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d188702, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188702, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188703 q = 1) : d129651 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d188703, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188703, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188704 q = 1) : d129652 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d188704, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188704, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188705 q = 1) : d129653 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d188705, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188705, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43710 (p : Pattern) (ha : d129672 p = 1) (hb : d188711 p = 1) : d129659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188706 q = 1) : d129654 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d188706, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43709 q ha hb
    | true =>
      simp only [d188706, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188707 q = 1) : d129655 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d188707, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188707, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188708 q = 1) : d129656 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d188708, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188708, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188709 q = 1) : d129657 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d188709, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188709, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188710 q = 1) : d129658 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d188710, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188710, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188711 q = 1) : d129659 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d188711, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188711, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43711 (p : Pattern) (ha : d129672 p = 1) (hb : d188717 p = 1) : d129665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188712 q = 1) : d129660 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d188712, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43710 q ha hb
    | true =>
      simp only [d188712, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188713 q = 1) : d129661 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d188713, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188713, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188714 q = 1) : d129662 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d188714, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188714, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188715 q = 1) : d129663 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d188715, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188715, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188716 q = 1) : d129664 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d188716, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188716, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188717 q = 1) : d129665 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d188717, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188717, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43712 (p : Pattern) (ha : d129672 p = 1) (hb : d188723 p = 1) : d129671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129672 q = 1) (hb : d188718 q = 1) : d129666 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d188718, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43711 q ha hb
    | true =>
      simp only [d188718, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129672 q = 1) (hb : d188719 q = 1) : d129667 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d188719, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188719, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129672 q = 1) (hb : d188720 q = 1) : d129668 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d188720, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188720, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129672 q = 1) (hb : d188721 q = 1) : d129669 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d188721, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188721, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129672 q = 1) (hb : d188722 q = 1) : d129670 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d188722, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188722, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129672 q = 1) (hb : d188723 q = 1) : d129671 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d188723, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188723, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43713 (p : Pattern) (ha : d9436 p = 1) (hb : d100998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9309 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
    | true =>
      simp only [d9309, d100960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9432 q = 1) (hb : d100994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d100994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9432, d100994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d100961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9433 q = 1) (hb : d100995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d100995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9433, d100995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9434 q = 1) (hb : d100996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d100996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d100996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9435 q = 1) (hb : d100997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d100997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d100997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9436 q = 1) (hb : d100998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d100998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d100998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43714 (p : Pattern) (ha : d101004 p = 1) (hb : d129477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d100999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d100999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d100999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43713 q ha hb
  have h2 (q : Pattern) (ha : d101000 q = 1) (hb : d129473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101000, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101000, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101001 q = 1) (hb : d129474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101001, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101001, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101002 q = 1) (hb : d129475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101002, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101002, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101003 q = 1) (hb : d129476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101003, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101003, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101004 q = 1) (hb : d129477 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101004, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101004, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43715 (p : Pattern) (ha : d101045 p = 1) (hb : d129487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9342 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d100993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43604 q ha hb
    | true =>
      simp only [d9342, d100993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43600 q ha hb
  have h3 (q : Pattern) (ha : d101035 q = 1) (hb : d129483 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101035, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101035, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101041 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101042 q = 1) (hb : d129484 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101042, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101042, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101043 q = 1) (hb : d129485 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101043, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101043, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101044 q = 1) (hb : d129486 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101044, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101044, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101045 q = 1) (hb : d129487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101045, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101045, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43716 (p : Pattern) (ha : d101057 p = 1) (hb : d129493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101046 q = 1) (hb : d129488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101046, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101046, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43715 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101053 q = 1) (hb : d129489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101053, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101053, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101054 q = 1) (hb : d129490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101054, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101054, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101055 q = 1) (hb : d129491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101055, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101055, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101056 q = 1) (hb : d129492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101056, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101056, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101057 q = 1) (hb : d129493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101057, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101057, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43717 (p : Pattern) (ha : d101063 p = 1) (hb : d129499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101005 q = 1) (hb : d129478 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101005, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101005, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43714 q ha hb
  have h3 (q : Pattern) (ha : d101006 q = 1) (hb : d129479 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101006, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101006, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101007 q = 1) (hb : d129480 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101007, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101007, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101008 q = 1) (hb : d129481 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101008, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101008, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101009 q = 1) (hb : d129482 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101009, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101009, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101058 q = 1) (hb : d129494 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101058, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101058, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43716 q ha hb
  have h8 (q : Pattern) (ha : d101059 q = 1) (hb : d129495 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101059, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101059, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101060 q = 1) (hb : d129496 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101060, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101060, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101061 q = 1) (hb : d129497 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101061, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101061, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101062 q = 1) (hb : d129498 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101062, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101062, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101063 q = 1) (hb : d129499 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101063, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101063, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43718 (p : Pattern) (ha : d101135 p = 1) (hb : d129505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101124 q = 1) (hb : d129500 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101124, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43620 q hb ha
    | true =>
      simp only [d101124, d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43615 q hb ha
  have h3 (q : Pattern) (ha : d101125 q = 1) (hb : d129501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101125, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101125, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101131 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101132 q = 1) (hb : d129502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101132, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101132, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101133 q = 1) (hb : d129503 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101133, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101133, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101134 q = 1) (hb : d129504 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101134, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101134, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101135 q = 1) (hb : d129505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101135, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101135, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43719 (p : Pattern) (ha : d101148 p = 1) (hb : d129511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101136 q = 1) (hb : d129506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101136, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101136, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43718 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101143 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101144 q = 1) (hb : d129507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101144, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101144, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101145 q = 1) (hb : d129508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101145, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101145, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101146 q = 1) (hb : d129509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101146, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101146, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101147 q = 1) (hb : d129510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101147, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101147, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101148 q = 1) (hb : d129511 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101148, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101148, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43720 (p : Pattern) (ha : d101154 p = 1) (hb : d129517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101149 q = 1) (hb : d129512 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101149, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101149, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43719 q ha hb
  have h2 (q : Pattern) (ha : d101150 q = 1) (hb : d129513 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101150, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101150, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101151 q = 1) (hb : d129514 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101151, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101151, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101152 q = 1) (hb : d129515 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101152, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101152, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101153 q = 1) (hb : d129516 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101153, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101153, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101154 q = 1) (hb : d129517 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101154, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101154, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43721 (p : Pattern) (ha : d101245 p = 1) (hb : d129524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101234 q = 1) (hb : d129519 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101234, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43631 q hb ha
    | true =>
      simp only [d101234, d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43626 q hb ha
  have h3 (q : Pattern) (ha : d101235 q = 1) (hb : d129520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101235, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101235, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101241 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101242 q = 1) (hb : d129521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101242, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101242, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101243 q = 1) (hb : d129522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101243, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101243, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101244 q = 1) (hb : d129523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101244, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101244, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101245 q = 1) (hb : d129524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101245, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101245, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43722 (p : Pattern) (ha : d101258 p = 1) (hb : d129530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101246 q = 1) (hb : d129525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101246, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101246, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43721 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101254 q = 1) (hb : d129526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101254, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101254, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101255 q = 1) (hb : d129527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101255, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101255, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101256 q = 1) (hb : d129528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101256, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101256, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101257 q = 1) (hb : d129529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101257, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101257, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101258 q = 1) (hb : d129530 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101258, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101258, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43723 (p : Pattern) (ha : d101264 p = 1) (hb : d129536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101259 q = 1) (hb : d129531 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101259, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101259, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43722 q ha hb
  have h2 (q : Pattern) (ha : d101260 q = 1) (hb : d129532 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101260, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101260, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101261 q = 1) (hb : d129533 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101261, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101261, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101262 q = 1) (hb : d129534 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101262, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101262, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101263 q = 1) (hb : d129535 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101263, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101263, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101264 q = 1) (hb : d129536 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101264, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101264, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43724 (p : Pattern) (ha : d101405 p = 1) (hb : d129540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h9 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101404 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101405 q = 1) (hb : d129540 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101405, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101405, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43725 (p : Pattern) (ha : d101411 p = 1) (hb : d129546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101406 q = 1) (hb : d129541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101406, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43724 q ha hb
    | true =>
      simp only [d101406, d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101407 q = 1) (hb : d129542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101407, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101407, d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d101397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43636 q ha hb
    | true =>
      simp only [d9876, d101397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d101398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d101398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101408 q = 1) (hb : d129543 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101408, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101408, d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101409 q = 1) (hb : d129544 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101409, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101409, d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101410 q = 1) (hb : d129545 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101410, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101410, d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101411 q = 1) (hb : d129546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101411, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101411, d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43726 (p : Pattern) (ha : d101436 p = 1) (hb : d129552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101416 q = 1) (hb : d129547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101416, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43725 q ha hb
    | true =>
      simp only [d101416, d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43637 q hb ha
  have h3 (q : Pattern) (ha : d101417 q = 1) (hb : d129548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101417, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101417, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101432 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101433 q = 1) (hb : d129549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101433, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101433, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101434 q = 1) (hb : d129550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101434, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101434, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101435 q = 1) (hb : d129551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101435, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101435, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101436 q = 1) (hb : d129552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101436, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101436, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43727 (p : Pattern) (ha : d101449 p = 1) (hb : d129558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101437 q = 1) (hb : d129553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101437, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101437, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43726 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101444 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101445 q = 1) (hb : d129554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101445, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101445, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101446 q = 1) (hb : d129555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101446, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101446, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101447 q = 1) (hb : d129556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101447, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101447, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101448 q = 1) (hb : d129557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101448, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101448, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101449 q = 1) (hb : d129558 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101449, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101449, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43728 (p : Pattern) (ha : d101455 p = 1) (hb : d129564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101450 q = 1) (hb : d129559 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101450, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101450, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43727 q ha hb
  have h2 (q : Pattern) (ha : d101451 q = 1) (hb : d129560 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101451, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101451, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101452 q = 1) (hb : d129561 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101452, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101452, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101453 q = 1) (hb : d129562 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101453, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101453, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101454 q = 1) (hb : d129563 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101454, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101454, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101455 q = 1) (hb : d129564 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101455, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101455, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43729 (p : Pattern) (ha : d101605 p = 1) (hb : d129569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h9 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101604 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101605 q = 1) (hb : d129569 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101605, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101605, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43730 (p : Pattern) (ha : d101611 p = 1) (hb : d129575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101606 q = 1) (hb : d129570 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101606, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43729 q ha hb
    | true =>
      simp only [d101606, d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101607 q = 1) (hb : d129571 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101607, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101607, d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d101597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43648 q ha hb
    | true =>
      simp only [d10170, d101597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d101598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d101598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101608 q = 1) (hb : d129572 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101608, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101608, d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101609 q = 1) (hb : d129573 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101609, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101609, d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101610 q = 1) (hb : d129574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101610, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101610, d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101611 q = 1) (hb : d129575 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101611, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101611, d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43731 (p : Pattern) (ha : d101636 p = 1) (hb : d129581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101616 q = 1) (hb : d129576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101616, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43730 q ha hb
    | true =>
      simp only [d101616, d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43649 q hb ha
  have h3 (q : Pattern) (ha : d101617 q = 1) (hb : d129577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101617, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101617, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101633 q = 1) (hb : d129578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101633, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101633, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101634 q = 1) (hb : d129579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101634, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101634, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101635 q = 1) (hb : d129580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101635, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101635, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101636 q = 1) (hb : d129581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101636, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101636, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43732 (p : Pattern) (ha : d101649 p = 1) (hb : d129587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101637 q = 1) (hb : d129582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101637, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101637, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43731 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101645 q = 1) (hb : d129583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101645, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101645, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101646 q = 1) (hb : d129584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101646, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101646, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101647 q = 1) (hb : d129585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101647, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101647, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101648 q = 1) (hb : d129586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101648, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101648, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101649 q = 1) (hb : d129587 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101649, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101649, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43733 (p : Pattern) (ha : d101655 p = 1) (hb : d129593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101650 q = 1) (hb : d129588 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101650, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101650, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43732 q ha hb
  have h2 (q : Pattern) (ha : d101651 q = 1) (hb : d129589 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101651, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101651, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101652 q = 1) (hb : d129590 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101652, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101652, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101653 q = 1) (hb : d129591 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101653, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101653, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101654 q = 1) (hb : d129592 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101654, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101654, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101655 q = 1) (hb : d129593 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101655, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101655, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43734 (p : Pattern) (ha : d101776 p = 1) (hb : d129599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h9 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101775 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101776 q = 1) (hb : d129599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101776, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101776, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43735 (p : Pattern) (ha : d101782 p = 1) (hb : d129605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101777 q = 1) (hb : d129600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101777, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43734 q ha hb
    | true =>
      simp only [d101777, d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101778 q = 1) (hb : d129601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101778, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101778, d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d101768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43660 q ha hb
    | true =>
      simp only [d10447, d101768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d101769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d101769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101779 q = 1) (hb : d129602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101779, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101779, d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101780 q = 1) (hb : d129603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101780, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101780, d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101781 q = 1) (hb : d129604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101781, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101781, d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101782 q = 1) (hb : d129605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101782, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101782, d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43736 (p : Pattern) (ha : d101807 p = 1) (hb : d129611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101787 q = 1) (hb : d129606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101787, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43735 q ha hb
    | true =>
      simp only [d101787, d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43661 q hb ha
  have h3 (q : Pattern) (ha : d101788 q = 1) (hb : d129607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101788, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101788, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101803 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101804 q = 1) (hb : d129608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101804, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101804, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101805 q = 1) (hb : d129609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101805, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101805, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101806 q = 1) (hb : d129610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101806, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101806, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101807 q = 1) (hb : d129611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101807, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101807, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43737 (p : Pattern) (ha : d101820 p = 1) (hb : d129617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101808 q = 1) (hb : d129612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101808, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101808, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43736 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101815 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101816 q = 1) (hb : d129613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101816, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101816, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101817 q = 1) (hb : d129614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101817, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101817, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101818 q = 1) (hb : d129615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101818, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101818, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101819 q = 1) (hb : d129616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101819, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101819, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101820 q = 1) (hb : d129617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101820, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101820, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43738 (p : Pattern) (ha : d101826 p = 1) (hb : d129623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101821 q = 1) (hb : d129618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101821, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101821, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43737 q ha hb
  have h2 (q : Pattern) (ha : d101822 q = 1) (hb : d129619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101822, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101822, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101823 q = 1) (hb : d129620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101823, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101823, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101824 q = 1) (hb : d129621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101824, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101824, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101825 q = 1) (hb : d129622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101825, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101825, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101826 q = 1) (hb : d129623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101826, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101826, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43739 (p : Pattern) (ha : d101832 p = 1) (hb : d129629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101155 q = 1) (hb : d129518 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101155, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43717 q ha hb
    | true =>
      simp only [d101155, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43720 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101265 q = 1) (hb : d129537 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101265, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101265, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43723 q ha hb
  have h3 (q : Pattern) (ha : d101266 q = 1) (hb : d129538 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101266, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101266, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101456 q = 1) (hb : d129565 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101456, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101456, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43728 q ha hb
  have h5 (q : Pattern) (ha : d101457 q = 1) (hb : d129566 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101457, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101457, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101458 q = 1) (hb : d129567 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101458, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101458, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101656 q = 1) (hb : d129594 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101656, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101656, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43733 q ha hb
  have h8 (q : Pattern) (ha : d101657 q = 1) (hb : d129595 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101657, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101657, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101658 q = 1) (hb : d129596 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101658, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101658, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101659 q = 1) (hb : d129597 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101659, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101659, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101827 q = 1) (hb : d129624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101827, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101827, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43738 q ha hb
  have h12 (q : Pattern) (ha : d101828 q = 1) (hb : d129625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101828, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101828, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101829 q = 1) (hb : d129626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101829, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101829, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101830 q = 1) (hb : d129627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101830, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101830, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101831 q = 1) (hb : d129628 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d101831, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d101831, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101832 q = 1) (hb : d129629 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d101832, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d101832, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43740 (p : Pattern) (ha : d101838 p = 1) (hb : d129635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101833 q = 1) (hb : d129630 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d101833, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43739 q ha hb
    | true =>
      simp only [d101833, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101834 q = 1) (hb : d129631 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d101834, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101834, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101835 q = 1) (hb : d129632 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d101835, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101835, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101836 q = 1) (hb : d129633 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d101836, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101836, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101837 q = 1) (hb : d129634 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d101837, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101837, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101838 q = 1) (hb : d129635 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d101838, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101838, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43741 (p : Pattern) (ha : d101844 p = 1) (hb : d129641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101839 q = 1) (hb : d129636 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d101839, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43740 q ha hb
    | true =>
      simp only [d101839, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101840 q = 1) (hb : d129637 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d101840, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101840, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101841 q = 1) (hb : d129638 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d101841, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101841, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101842 q = 1) (hb : d129639 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d101842, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101842, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101843 q = 1) (hb : d129640 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d101843, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101843, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101844 q = 1) (hb : d129641 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d101844, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101844, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43742 (p : Pattern) (ha : d101850 p = 1) (hb : d129647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101845 q = 1) (hb : d129642 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d101845, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43741 q ha hb
    | true =>
      simp only [d101845, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101846 q = 1) (hb : d129643 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d101846, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101846, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101847 q = 1) (hb : d129644 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d101847, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101847, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101848 q = 1) (hb : d129645 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d101848, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101848, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101849 q = 1) (hb : d129646 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d101849, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101849, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101850 q = 1) (hb : d129647 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d101850, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101850, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43743 (p : Pattern) (ha : d101856 p = 1) (hb : d129653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101851 q = 1) (hb : d129648 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d101851, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43742 q ha hb
    | true =>
      simp only [d101851, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101852 q = 1) (hb : d129649 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d101852, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101852, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101853 q = 1) (hb : d129650 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d101853, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101853, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101854 q = 1) (hb : d129651 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d101854, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101854, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101855 q = 1) (hb : d129652 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d101855, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101855, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101856 q = 1) (hb : d129653 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d101856, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101856, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43744 (p : Pattern) (ha : d101862 p = 1) (hb : d129659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101857 q = 1) (hb : d129654 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d101857, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43743 q ha hb
    | true =>
      simp only [d101857, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101858 q = 1) (hb : d129655 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d101858, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101858, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101859 q = 1) (hb : d129656 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d101859, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101859, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101860 q = 1) (hb : d129657 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d101860, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101860, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101861 q = 1) (hb : d129658 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d101861, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101861, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101862 q = 1) (hb : d129659 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d101862, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101862, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43745 (p : Pattern) (ha : d101868 p = 1) (hb : d129665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101863 q = 1) (hb : d129660 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d101863, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43744 q ha hb
    | true =>
      simp only [d101863, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101864 q = 1) (hb : d129661 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d101864, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101864, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101865 q = 1) (hb : d129662 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d101865, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101865, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101866 q = 1) (hb : d129663 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d101866, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101866, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101867 q = 1) (hb : d129664 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d101867, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101867, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101868 q = 1) (hb : d129665 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d101868, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101868, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43746 (p : Pattern) (ha : d101874 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101869 q = 1) (hb : d129666 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d101869, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43745 q ha hb
    | true =>
      simp only [d101869, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101870 q = 1) (hb : d129667 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d101870, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101870, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101871 q = 1) (hb : d129668 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d101871, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101871, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101872 q = 1) (hb : d129669 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d101872, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101872, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101873 q = 1) (hb : d129670 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d101873, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101873, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101874 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d101874, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101874, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43747 (p : Pattern) (ha : d9436 p = 1) (hb : d101879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9309 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9432 q = 1) (hb : d101875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9432, d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9310 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9433 q = 1) (hb : d101876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9433, d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9434 q = 1) (hb : d101877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9435 q = 1) (hb : d101878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9436 q = 1) (hb : d101879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43748 (p : Pattern) (ha : d101885 p = 1) (hb : d129477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d101880 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43747 q ha hb
  have h2 (q : Pattern) (ha : d101881 q = 1) (hb : d129473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101881, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101881, d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d101882 q = 1) (hb : d129474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101882, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101882, d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d101883 q = 1) (hb : d129475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101883, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101883, d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101884 q = 1) (hb : d129476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101884, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101884, d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101885 q = 1) (hb : d129477 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101885, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101885, d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43749 (p : Pattern) (ha : d101895 p = 1) (hb : d129487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9342 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101891 q = 1) (hb : d129483 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101891, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101891, d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9426 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101892 q = 1) (hb : d129484 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101892, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101892, d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101893 q = 1) (hb : d129485 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101893, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101893, d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101894 q = 1) (hb : d129486 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101894, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101894, d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101895 q = 1) (hb : d129487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101895, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101895, d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
