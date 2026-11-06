import NetHack.Soko22Hazard87.AndIntroBlocks0032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro8250 (p : Pattern) (ha : d1326 p = 1) (hb : d77844 p = 1) : d80035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1156 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1182 q = 1) (hb : d77844 q = 1) : d80012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1326 q = 1) (hb : d77844 q = 1) : d80035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1326, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8251 (p : Pattern) (ha : d1332 p = 1) (hb : d77844 p = 1) : d80040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1190 q = 1) (hb : d77844 q = 1) : d80018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1191 q = 1) (hb : d77844 q = 1) : d80019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1191, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1332 q = 1) (hb : d77844 q = 1) : d80040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1332, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8252 (p : Pattern) (ha : d1337 p = 1) (hb : d77844 p = 1) : d80044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1224 q = 1) (hb : d77844 q = 1) : d80024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1224, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d77844 q = 1) : d80025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1225, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d77844 q = 1) : d80026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1337 q = 1) (hb : d77844 q = 1) : d80044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1337, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8253 (p : Pattern) (ha : d69597 p = 1) (hb : d77845 p = 1) : d80051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4980 q = 1) (hb : d77845 q = 1) : d80014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4980, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8245 q ha hb
    | true =>
      simp only [d4980, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4981 q = 1) (hb : d77845 q = 1) : d80015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4981, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4981, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4982 q = 1) (hb : d77845 q = 1) : d80016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4982, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4982, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4983 q = 1) (hb : d77845 q = 1) : d80017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4983, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4983, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4984 q = 1) (hb : d77845 q = 1) : d80021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4984, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8246 q ha hb
    | true =>
      simp only [d4984, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4985 q = 1) (hb : d77845 q = 1) : d80022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4985, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4985, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4986 q = 1) (hb : d77845 q = 1) : d80023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4986, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4986, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4987 q = 1) (hb : d77845 q = 1) : d80028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8248 q ha hb
    | true =>
      simp only [d4987, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69588 q = 1) (hb : d77845 q = 1) : d80029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69588, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69588, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1320 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8239 q ha hb
    | true =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1321 q = 1) (hb : d77845 q = 1) : d80030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1321, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69589 q = 1) (hb : d77845 q = 1) : d80031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69589, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69589, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69590 q = 1) (hb : d77845 q = 1) : d80032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69590, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69591 q = 1) (hb : d77845 q = 1) : d80033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69591, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4994 q = 1) (hb : d77845 q = 1) : d80036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4994, d77845, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8250 q ha hb
    | true =>
      simp only [d4994, d77845, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d4995 q = 1) (hb : d77845 q = 1) : d80037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4995, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4995, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4996 q = 1) (hb : d77845 q = 1) : d80038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4996, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4996, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4997 q = 1) (hb : d77845 q = 1) : d80039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4997, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4997, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4998 q = 1) (hb : d77845 q = 1) : d80041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4998, d77845, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8251 q ha hb
    | true =>
      simp only [d4998, d77845, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d4999 q = 1) (hb : d77845 q = 1) : d80042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4999, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4999, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5000 q = 1) (hb : d77845 q = 1) : d80043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5000, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5000, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5001 q = 1) (hb : d77845 q = 1) : d80045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8252 q ha hb
    | true =>
      simp only [d5001, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69593 q = 1) (hb : d77845 q = 1) : d80046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69593, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69593, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1343 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8241 q ha hb
    | true =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d1344 q = 1) (hb : d77845 q = 1) : d80047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d1344, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69594 q = 1) (hb : d77845 q = 1) : d80048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69594, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69594, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69595 q = 1) (hb : d77845 q = 1) : d80049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69595, d80049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69595, d80049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69596 q = 1) (hb : d77845 q = 1) : d80050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69596, d80050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69596, d80050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69597 q = 1) (hb : d77845 q = 1) : d80051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69597, d80051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69597, d80051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8254 (p : Pattern) (ha : d69604 p = 1) (hb : d77845 p = 1) : d80058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5001 q = 1) (hb : d77845 q = 1) : d80045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8252 q ha hb
    | true =>
      simp only [d5001, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69593 q = 1) (hb : d77845 q = 1) : d80046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69593, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69593, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1343 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8241 q ha hb
    | true =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1344 q = 1) (hb : d77845 q = 1) : d80047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1344, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69594 q = 1) (hb : d77845 q = 1) : d80048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69594, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69594, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69602 q = 1) (hb : d77845 q = 1) : d80056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69602, d80056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69602, d80056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69603 q = 1) (hb : d77845 q = 1) : d80057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69603, d80057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69603, d80057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69604 q = 1) (hb : d77845 q = 1) : d80058 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69604, d80058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69604, d80058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8255 (p : Pattern) (ha : d1422 p = 1) (hb : d77842 p = 1) : d7834 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1415 q = 1) : d1415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1421 q = 1) (hb : d77842 q = 1) : d7833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d77842, d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1421, d77842, d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1422 q = 1) (hb : d77842 q = 1) : d7834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d7834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1422, d7834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8256 (p : Pattern) (ha : d1428 p = 1) (hb : d77844 p = 1) : d80067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1419 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1423 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8255 q ha hb
    | true =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1424 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1425 q = 1) (hb : d77844 q = 1) : d80064 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d77844, d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1425, d77844, d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1426 q = 1) (hb : d77844 q = 1) : d80065 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1426, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1427 q = 1) (hb : d77844 q = 1) : d80066 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1427, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1428 q = 1) (hb : d77844 q = 1) : d80067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1428, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8257 (p : Pattern) (ha : d1436 p = 1) (hb : d77844 p = 1) : d80073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1424 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1432 q = 1) (hb : d77842 q = 1) : d1432 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1433 q = 1) (hb : d77844 q = 1) : d80070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d77844, d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1433, d77844, d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1434 q = 1) (hb : d77844 q = 1) : d80071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1434, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1435 q = 1) (hb : d77844 q = 1) : d80072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1435, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1436 q = 1) (hb : d77844 q = 1) : d80073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1436, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8258 (p : Pattern) (ha : d69614 p = 1) (hb : d77845 p = 1) : d80079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5054 q = 1) (hb : d77845 q = 1) : d80068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5054, d77845, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8256 q ha hb
    | true =>
      simp only [d5054, d77845, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69610 q = 1) (hb : d77845 q = 1) : d80069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69610, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69610, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1487 q = 1) (hb : d77845 q = 1) : d80074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d77845, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8257 q ha hb
    | true =>
      simp only [d1487, d77845, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1488 q = 1) (hb : d77845 q = 1) : d80075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d80075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1488, d80075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69611 q = 1) (hb : d77845 q = 1) : d80076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69611, d80076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69611, d80076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69612 q = 1) (hb : d77845 q = 1) : d80077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69612, d80077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69612, d80077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69613 q = 1) (hb : d77845 q = 1) : d80078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69613, d80078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69613, d80078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69614 q = 1) (hb : d77845 q = 1) : d80079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69614, d80079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69614, d80079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8259 (p : Pattern) (ha : d70046 p = 1) (hb : d77845 p = 1) : d80085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4970 q = 1) (hb : d77845 q = 1) : d80000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4970, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4970, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8240 q ha hb
  have h2 (q : Pattern) (ha : d4971 q = 1) (hb : d77845 q = 1) : d80001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4971, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4971, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4977 q = 1) (hb : d77845 q = 1) : d80009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8240 q ha hb
    | true =>
      simp only [d4977, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8242 q ha hb
  have h4 (q : Pattern) (ha : d4978 q = 1) (hb : d77845 q = 1) : d80010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4978, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4979 q = 1) (hb : d77845 q = 1) : d80011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4979, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4979, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69598 q = 1) (hb : d77845 q = 1) : d80052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69598, d80052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8249 q ha hb
    | true =>
      simp only [d69598, d80052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8253 q ha hb
  have h7 (q : Pattern) (ha : d5042 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8244 q ha hb
    | true =>
      simp only [d5042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8235 q ha hb
  have h8 (q : Pattern) (ha : d70035 q = 1) (hb : d77845 q = 1) : d80053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70035, d80053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70035, d80053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70036 q = 1) (hb : d77845 q = 1) : d80054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70036, d80054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70036, d80054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70037 q = 1) (hb : d77845 q = 1) : d80055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70037, d80055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70037, d80055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69605 q = 1) (hb : d77845 q = 1) : d80059 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69605, d80059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69605, d80059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8254 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8236 q ha hb
  have h13 (q : Pattern) (ha : d70038 q = 1) (hb : d77845 q = 1) : d80060 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70038, d80060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70038, d80060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70039 q = 1) (hb : d77845 q = 1) : d80061 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70039, d80061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70039, d80061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70040 q = 1) (hb : d77845 q = 1) : d80062 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70040, d80062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70040, d80062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70041 q = 1) (hb : d77845 q = 1) : d80063 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70041, d80063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70041, d80063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69615 q = 1) (hb : d77845 q = 1) : d80080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69615, d80080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69615, d80080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8258 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8238 q ha hb
  have h19 (q : Pattern) (ha : d70042 q = 1) (hb : d77845 q = 1) : d80081 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70042, d80081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70042, d80081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70043 q = 1) (hb : d77845 q = 1) : d80082 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70043, d80082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70043, d80082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70044 q = 1) (hb : d77845 q = 1) : d80083 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70044, d80083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70044, d80083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70045 q = 1) (hb : d77845 q = 1) : d80084 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70045, d80084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70045, d80084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70046 q = 1) (hb : d77845 q = 1) : d80085 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70046, d80085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70046, d80085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8260 (p : Pattern) (ha : d70052 p = 1) (hb : d77845 p = 1) : d80091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70047 q = 1) (hb : d77845 q = 1) : d80086 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70047, d80086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70047, d80086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8259 q ha hb
  have h2 (q : Pattern) (ha : d70048 q = 1) (hb : d77845 q = 1) : d80087 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70048, d80087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70048, d80087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70049 q = 1) (hb : d77845 q = 1) : d80088 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70049, d80088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70049, d80088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70050 q = 1) (hb : d77845 q = 1) : d80089 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70050, d80089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70050, d80089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70051 q = 1) (hb : d77845 q = 1) : d80090 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70051, d80090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70051, d80090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70052 q = 1) (hb : d77845 q = 1) : d80091 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70052, d80091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70052, d80091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8261 (p : Pattern) (ha : d1623 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1620, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8262 (p : Pattern) (ha : d1633 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1620 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1620, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8263 (p : Pattern) (ha : d1838 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1827 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8261 q ha hb
    | true =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1828 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1829 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1830 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1831 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1833 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8262 q ha hb
    | true =>
      simp only [d1833, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1834 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1835 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1836 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1837 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1838 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8264 (p : Pattern) (ha : d1847 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1833 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8262 q ha hb
    | true =>
      simp only [d1833, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1835 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1836 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1837 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1847 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8265 (p : Pattern) (ha : d1974 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1971 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1971, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8266 (p : Pattern) (ha : d1980 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1975 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8265 q ha hb
    | true =>
      simp only [d1975, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1976 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1977 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1978 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1979 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1980 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8267 (p : Pattern) (ha : d1619 p = 1) (hb : d77844 p = 1) : d80098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1618 q = 1) (hb : d77844 q = 1) : d80097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1618, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1619 q = 1) (hb : d77844 q = 1) : d80098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8268 (p : Pattern) (ha : d5080 p = 1) (hb : d77845 p = 1) : d80104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1797 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8267 q ha hb
    | true =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d77845 q = 1) : d80100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5076, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d77845 q = 1) : d80101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d77845 q = 1) : d80102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d77845 q = 1) : d80103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5080 q = 1) (hb : d77845 q = 1) : d80104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5080, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5080, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8269 (p : Pattern) (ha : d1632 p = 1) (hb : d77844 p = 1) : d80107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1618 q = 1) (hb : d77844 q = 1) : d80097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1618, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1632 q = 1) (hb : d77844 q = 1) : d80107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1632, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8270 (p : Pattern) (ha : d5087 p = 1) (hb : d77845 p = 1) : d80113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1797 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8267 q ha hb
    | true =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d77845 q = 1) : d80100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5076, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d77845 q = 1) : d80101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d77845 q = 1) : d80102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d77845 q = 1) : d80103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1820 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8269 q ha hb
    | true =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5083 q = 1) (hb : d77845 q = 1) : d80109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5083, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5084 q = 1) (hb : d77845 q = 1) : d80110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5084, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5085 q = 1) (hb : d77845 q = 1) : d80111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5086 q = 1) (hb : d77845 q = 1) : d80112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5087 q = 1) (hb : d77845 q = 1) : d80113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5087, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5087, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8271 (p : Pattern) (ha : d5151 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5148 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5148, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5149 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5150 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5151 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8272 (p : Pattern) (ha : d5157 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5152 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5152, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8271 q ha hb
    | true =>
      simp only [d5152, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5153 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5154 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5155 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5156 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1827 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8261 q ha hb
    | true =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1828 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1829 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1830 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1831 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5157 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8273 (p : Pattern) (ha : d1644 p = 1) (hb : d77844 p = 1) : d80118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1643 q = 1) (hb : d77844 q = 1) : d80117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1644 q = 1) (hb : d77844 q = 1) : d80118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8274 (p : Pattern) (ha : d1653 p = 1) (hb : d77844 p = 1) : d80125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1651 q = 1) (hb : d77844 q = 1) : d80123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1652 q = 1) (hb : d77844 q = 1) : d80124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1652, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1653 q = 1) (hb : d77844 q = 1) : d80125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8275 (p : Pattern) (ha : d1609 p = 1) (hb : d77842 p = 1) : d7882 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1606 q = 1) : d1606 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1608 q = 1) (hb : d77842 q = 1) : d7881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d77842, d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1608, d77842, d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1609 q = 1) (hb : d77842 q = 1) : d7882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d7882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1609, d7882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8276 (p : Pattern) (ha : d1682 p = 1) (hb : d77844 p = 1) : d80132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d77844 q = 1) : d80129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1679, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d77844 q = 1) : d80130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d77844 q = 1) : d80131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1682 q = 1) (hb : d77844 q = 1) : d80132 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8277 (p : Pattern) (ha : d69634 p = 1) (hb : d77845 p = 1) : d80139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5091 q = 1) (hb : d77845 q = 1) : d80119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5091, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8273 q ha hb
    | true =>
      simp only [d5091, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5092 q = 1) (hb : d77845 q = 1) : d80120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5092, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5092, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5093 q = 1) (hb : d77845 q = 1) : d80121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5093, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5093, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5094 q = 1) (hb : d77845 q = 1) : d80122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5094, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5094, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5095 q = 1) (hb : d77845 q = 1) : d80126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5095, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8274 q ha hb
    | true =>
      simp only [d5095, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5096 q = 1) (hb : d77845 q = 1) : d80127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5096, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5096, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5097 q = 1) (hb : d77845 q = 1) : d80128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5097, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5097, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5098 q = 1) (hb : d77845 q = 1) : d80133 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8276 q ha hb
    | true =>
      simp only [d5098, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69630 q = 1) (hb : d77845 q = 1) : d80134 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69630, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69630, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1797 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8267 q ha hb
    | true =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1798 q = 1) (hb : d77845 q = 1) : d80135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1798, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69631 q = 1) (hb : d77845 q = 1) : d80136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69631, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69631, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69632 q = 1) (hb : d77845 q = 1) : d80137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69632, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69633 q = 1) (hb : d77845 q = 1) : d80138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69633, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69634 q = 1) (hb : d77845 q = 1) : d80139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69634, d80139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69634, d80139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8278 (p : Pattern) (ha : d1803 p = 1) (hb : d77844 p = 1) : d80140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1617 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1617, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1643 q = 1) (hb : d77844 q = 1) : d80117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1803 q = 1) (hb : d77844 q = 1) : d80140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1803, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8279 (p : Pattern) (ha : d1809 p = 1) (hb : d77844 p = 1) : d80145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1616 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1616, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1651 q = 1) (hb : d77844 q = 1) : d80123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1652 q = 1) (hb : d77844 q = 1) : d80124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1652, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1809 q = 1) (hb : d77844 q = 1) : d80145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1809, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8280 (p : Pattern) (ha : d1814 p = 1) (hb : d77844 p = 1) : d80149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1678 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1679 q = 1) (hb : d77844 q = 1) : d80129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1679, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d77844 q = 1) : d80130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1680, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d77844 q = 1) : d80131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1814 q = 1) (hb : d77844 q = 1) : d80149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1814, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8281 (p : Pattern) (ha : d69639 p = 1) (hb : d77845 p = 1) : d80156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5091 q = 1) (hb : d77845 q = 1) : d80119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5091, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8273 q ha hb
    | true =>
      simp only [d5091, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5092 q = 1) (hb : d77845 q = 1) : d80120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5092, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5092, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5093 q = 1) (hb : d77845 q = 1) : d80121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5093, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5093, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5094 q = 1) (hb : d77845 q = 1) : d80122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5094, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5094, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5095 q = 1) (hb : d77845 q = 1) : d80126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5095, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8274 q ha hb
    | true =>
      simp only [d5095, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5096 q = 1) (hb : d77845 q = 1) : d80127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5096, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5096, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5097 q = 1) (hb : d77845 q = 1) : d80128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5097, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5097, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5098 q = 1) (hb : d77845 q = 1) : d80133 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8276 q ha hb
    | true =>
      simp only [d5098, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69630 q = 1) (hb : d77845 q = 1) : d80134 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69630, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69630, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1797 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8267 q ha hb
    | true =>
      simp only [d1797, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1798 q = 1) (hb : d77845 q = 1) : d80135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1798, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69631 q = 1) (hb : d77845 q = 1) : d80136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69631, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69631, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69632 q = 1) (hb : d77845 q = 1) : d80137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69632, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69632, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69633 q = 1) (hb : d77845 q = 1) : d80138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69633, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69633, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5105 q = 1) (hb : d77845 q = 1) : d80141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5105, d77845, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8278 q ha hb
    | true =>
      simp only [d5105, d77845, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d5106 q = 1) (hb : d77845 q = 1) : d80142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5106, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5106, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5107 q = 1) (hb : d77845 q = 1) : d80143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5107, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5107, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d5108 q = 1) (hb : d77845 q = 1) : d80144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5108, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5108, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5109 q = 1) (hb : d77845 q = 1) : d80146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5109, d77845, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8279 q ha hb
    | true =>
      simp only [d5109, d77845, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d5110 q = 1) (hb : d77845 q = 1) : d80147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5110, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5110, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5111 q = 1) (hb : d77845 q = 1) : d80148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5111, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5111, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5112 q = 1) (hb : d77845 q = 1) : d80150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8280 q ha hb
    | true =>
      simp only [d5112, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69635 q = 1) (hb : d77845 q = 1) : d80151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69635, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69635, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1820 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8269 q ha hb
    | true =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d1821 q = 1) (hb : d77845 q = 1) : d80152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d1821, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69636 q = 1) (hb : d77845 q = 1) : d80153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69636, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69636, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69637 q = 1) (hb : d77845 q = 1) : d80154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69637, d80154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69637, d80154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69638 q = 1) (hb : d77845 q = 1) : d80155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69638, d80155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69638, d80155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69639 q = 1) (hb : d77845 q = 1) : d80156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69639, d80156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69639, d80156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8282 (p : Pattern) (ha : d69646 p = 1) (hb : d77845 p = 1) : d80163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5112 q = 1) (hb : d77845 q = 1) : d80150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8280 q ha hb
    | true =>
      simp only [d5112, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69635 q = 1) (hb : d77845 q = 1) : d80151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69635, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69635, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1820 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8269 q ha hb
    | true =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1821 q = 1) (hb : d77845 q = 1) : d80152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1821, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69636 q = 1) (hb : d77845 q = 1) : d80153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69636, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69636, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69644 q = 1) (hb : d77845 q = 1) : d80161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69644, d80161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69644, d80161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69645 q = 1) (hb : d77845 q = 1) : d80162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69645, d80162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69645, d80162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69646 q = 1) (hb : d77845 q = 1) : d80163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69646, d80163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69646, d80163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8283 (p : Pattern) (ha : d1899 p = 1) (hb : d77842 p = 1) : d7988 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1892 q = 1) : d1892 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1898 q = 1) (hb : d77842 q = 1) : d7987 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d77842, d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1898, d77842, d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1899 q = 1) (hb : d77842 q = 1) : d7988 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d7988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1899, d7988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8284 (p : Pattern) (ha : d1905 p = 1) (hb : d77844 p = 1) : d80172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1896 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1900 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8283 q ha hb
    | true =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1901 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1902 q = 1) (hb : d77844 q = 1) : d80169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d77844, d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1902, d77844, d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1903 q = 1) (hb : d77844 q = 1) : d80170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1903, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1904 q = 1) (hb : d77844 q = 1) : d80171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1904, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1905 q = 1) (hb : d77844 q = 1) : d80172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1905, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8285 (p : Pattern) (ha : d1913 p = 1) (hb : d77844 p = 1) : d80178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1909 q = 1) (hb : d77842 q = 1) : d1909 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1910 q = 1) (hb : d77844 q = 1) : d80175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d77844, d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1910, d77844, d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1911 q = 1) (hb : d77844 q = 1) : d80176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1911, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1912 q = 1) (hb : d77844 q = 1) : d80177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1912, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1913 q = 1) (hb : d77844 q = 1) : d80178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1913, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8286 (p : Pattern) (ha : d69656 p = 1) (hb : d77845 p = 1) : d80184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5170 q = 1) (hb : d77845 q = 1) : d80173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5170, d77845, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8284 q ha hb
    | true =>
      simp only [d5170, d77845, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69652 q = 1) (hb : d77845 q = 1) : d80174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69652, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69652, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1964 q = 1) (hb : d77845 q = 1) : d80179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d77845, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8285 q ha hb
    | true =>
      simp only [d1964, d77845, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1965 q = 1) (hb : d77845 q = 1) : d80180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d80180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1965, d80180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69653 q = 1) (hb : d77845 q = 1) : d80181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69653, d80181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69653, d80181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69654 q = 1) (hb : d77845 q = 1) : d80182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69654, d80182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69654, d80182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69655 q = 1) (hb : d77845 q = 1) : d80183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69655, d80183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69655, d80183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69656 q = 1) (hb : d77845 q = 1) : d80184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69656, d80184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69656, d80184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8287 (p : Pattern) (ha : d70067 p = 1) (hb : d77845 p = 1) : d80190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5081 q = 1) (hb : d77845 q = 1) : d80105 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5081, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5081, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8268 q ha hb
  have h2 (q : Pattern) (ha : d5082 q = 1) (hb : d77845 q = 1) : d80106 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5082, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5082, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5088 q = 1) (hb : d77845 q = 1) : d80114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8268 q ha hb
    | true =>
      simp only [d5088, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8270 q ha hb
  have h4 (q : Pattern) (ha : d5089 q = 1) (hb : d77845 q = 1) : d80115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5089, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5090 q = 1) (hb : d77845 q = 1) : d80116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5090, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5090, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69640 q = 1) (hb : d77845 q = 1) : d80157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69640, d80157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8277 q ha hb
    | true =>
      simp only [d69640, d80157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8281 q ha hb
  have h7 (q : Pattern) (ha : d5158 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8272 q ha hb
    | true =>
      simp only [d5158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8263 q ha hb
  have h8 (q : Pattern) (ha : d70056 q = 1) (hb : d77845 q = 1) : d80158 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70056, d80158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70056, d80158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70057 q = 1) (hb : d77845 q = 1) : d80159 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70057, d80159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70057, d80159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70058 q = 1) (hb : d77845 q = 1) : d80160 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70058, d80160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70058, d80160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69647 q = 1) (hb : d77845 q = 1) : d80164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69647, d80164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69647, d80164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8282 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8264 q ha hb
  have h13 (q : Pattern) (ha : d70059 q = 1) (hb : d77845 q = 1) : d80165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70059, d80165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70059, d80165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70060 q = 1) (hb : d77845 q = 1) : d80166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70060, d80166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70060, d80166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70061 q = 1) (hb : d77845 q = 1) : d80167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70061, d80167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70061, d80167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70062 q = 1) (hb : d77845 q = 1) : d80168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70062, d80168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70062, d80168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69657 q = 1) (hb : d77845 q = 1) : d80185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69657, d80185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69657, d80185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8286 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8266 q ha hb
  have h19 (q : Pattern) (ha : d70063 q = 1) (hb : d77845 q = 1) : d80186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70063, d80186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70063, d80186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70064 q = 1) (hb : d77845 q = 1) : d80187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70064, d80187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70064, d80187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70065 q = 1) (hb : d77845 q = 1) : d80188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70065, d80188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70065, d80188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70066 q = 1) (hb : d77845 q = 1) : d80189 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70066, d80189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70066, d80189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70067 q = 1) (hb : d77845 q = 1) : d80190 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70067, d80190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70067, d80190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8288 (p : Pattern) (ha : d70073 p = 1) (hb : d77845 p = 1) : d80196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70068 q = 1) (hb : d77845 q = 1) : d80191 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70068, d80191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70068, d80191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8287 q ha hb
  have h2 (q : Pattern) (ha : d70069 q = 1) (hb : d77845 q = 1) : d80192 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70069, d80192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70069, d80192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70070 q = 1) (hb : d77845 q = 1) : d80193 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70070, d80193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70070, d80193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70071 q = 1) (hb : d77845 q = 1) : d80194 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70071, d80194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70071, d80194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70072 q = 1) (hb : d77845 q = 1) : d80195 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70072, d80195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70072, d80195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70073 q = 1) (hb : d77845 q = 1) : d80196 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70073, d80196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70073, d80196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8289 (p : Pattern) (ha : d2106 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2103, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8290 (p : Pattern) (ha : d2116 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2103 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2103, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8291 (p : Pattern) (ha : d2316 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2305 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8289 q ha hb
    | true =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2306 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2307 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2308 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2309 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2311 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8290 q ha hb
    | true =>
      simp only [d2311, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2312 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2313 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2314 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2315 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2316 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8292 (p : Pattern) (ha : d2325 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2311 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8290 q ha hb
    | true =>
      simp only [d2311, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2313 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2314 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2315 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2325 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8293 (p : Pattern) (ha : d2452 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2449 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2449, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8294 (p : Pattern) (ha : d2458 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2453 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8293 q ha hb
    | true =>
      simp only [d2453, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2454 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2455 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2456 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2457 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2458 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8295 (p : Pattern) (ha : d2102 p = 1) (hb : d77844 p = 1) : d80204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2101 q = 1) (hb : d77844 q = 1) : d80203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2101, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2102 q = 1) (hb : d77844 q = 1) : d80204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8296 (p : Pattern) (ha : d5197 p = 1) (hb : d77845 p = 1) : d80210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2275 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8295 q ha hb
    | true =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d77845 q = 1) : d80206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5193, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d77845 q = 1) : d80207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d77845 q = 1) : d80208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d77845 q = 1) : d80209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5197 q = 1) (hb : d77845 q = 1) : d80210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5197, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5197, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8297 (p : Pattern) (ha : d2115 p = 1) (hb : d77844 p = 1) : d80213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2101 q = 1) (hb : d77844 q = 1) : d80203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2101, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2115 q = 1) (hb : d77844 q = 1) : d80213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2115, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8298 (p : Pattern) (ha : d5204 p = 1) (hb : d77845 p = 1) : d80219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2275 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8295 q ha hb
    | true =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d77845 q = 1) : d80206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5193, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d77845 q = 1) : d80207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d77845 q = 1) : d80208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d77845 q = 1) : d80209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2298 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8297 q ha hb
    | true =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5200 q = 1) (hb : d77845 q = 1) : d80215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5200, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5201 q = 1) (hb : d77845 q = 1) : d80216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5201, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5202 q = 1) (hb : d77845 q = 1) : d80217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5203 q = 1) (hb : d77845 q = 1) : d80218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5204 q = 1) (hb : d77845 q = 1) : d80219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5204, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5204, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8299 (p : Pattern) (ha : d5264 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5261 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5261, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5262 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5263 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5264 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8300 (p : Pattern) (ha : d5270 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5265 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5265, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8299 q ha hb
    | true =>
      simp only [d5265, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5266 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5267 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5268 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5269 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2305 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8289 q ha hb
    | true =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2306 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2307 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2308 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2309 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5270 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8301 (p : Pattern) (ha : d2127 p = 1) (hb : d77844 p = 1) : d80224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2126 q = 1) (hb : d77844 q = 1) : d80223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2127 q = 1) (hb : d77844 q = 1) : d80224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8302 (p : Pattern) (ha : d2136 p = 1) (hb : d77844 p = 1) : d80231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2134 q = 1) (hb : d77844 q = 1) : d80229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2135 q = 1) (hb : d77844 q = 1) : d80230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2135, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2136 q = 1) (hb : d77844 q = 1) : d80231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8303 (p : Pattern) (ha : d2092 p = 1) (hb : d77842 p = 1) : d8037 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2089 q = 1) : d2089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2091 q = 1) (hb : d77842 q = 1) : d8036 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d77842, d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2091, d77842, d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2092 q = 1) (hb : d77842 q = 1) : d8037 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d8037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2092, d8037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8304 (p : Pattern) (ha : d2161 p = 1) (hb : d77844 p = 1) : d80238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2157 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d77844 q = 1) : d80235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2158, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d77844 q = 1) : d80236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d77844 q = 1) : d80237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2161 q = 1) (hb : d77844 q = 1) : d80238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8305 (p : Pattern) (ha : d69677 p = 1) (hb : d77845 p = 1) : d80245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5208 q = 1) (hb : d77845 q = 1) : d80225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5208, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8301 q ha hb
    | true =>
      simp only [d5208, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5209 q = 1) (hb : d77845 q = 1) : d80226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5209, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5209, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5210 q = 1) (hb : d77845 q = 1) : d80227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5210, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5210, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5211 q = 1) (hb : d77845 q = 1) : d80228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5211, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5211, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5212 q = 1) (hb : d77845 q = 1) : d80232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5212, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8302 q ha hb
    | true =>
      simp only [d5212, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5213 q = 1) (hb : d77845 q = 1) : d80233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5213, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5213, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5214 q = 1) (hb : d77845 q = 1) : d80234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5214, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5214, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5215 q = 1) (hb : d77845 q = 1) : d80239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8304 q ha hb
    | true =>
      simp only [d5215, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69673 q = 1) (hb : d77845 q = 1) : d80240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69673, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69673, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8295 q ha hb
    | true =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d77845 q = 1) : d80241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69674 q = 1) (hb : d77845 q = 1) : d80242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69674, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69674, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69675 q = 1) (hb : d77845 q = 1) : d80243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69675, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69676 q = 1) (hb : d77845 q = 1) : d80244 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69676, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69677 q = 1) (hb : d77845 q = 1) : d80245 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69677, d80245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69677, d80245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8306 (p : Pattern) (ha : d2281 p = 1) (hb : d77844 p = 1) : d80246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2100 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2100, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2126 q = 1) (hb : d77844 q = 1) : d80223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2281 q = 1) (hb : d77844 q = 1) : d80246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2281, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8307 (p : Pattern) (ha : d2287 p = 1) (hb : d77844 p = 1) : d80251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2099 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2099, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2134 q = 1) (hb : d77844 q = 1) : d80229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2135 q = 1) (hb : d77844 q = 1) : d80230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2135, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2287 q = 1) (hb : d77844 q = 1) : d80251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2287, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8308 (p : Pattern) (ha : d2292 p = 1) (hb : d77844 p = 1) : d80255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2158 q = 1) (hb : d77844 q = 1) : d80235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2158, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d77844 q = 1) : d80236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2159, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d77844 q = 1) : d80237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2292 q = 1) (hb : d77844 q = 1) : d80255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2292, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2292, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8309 (p : Pattern) (ha : d69682 p = 1) (hb : d77845 p = 1) : d80262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5208 q = 1) (hb : d77845 q = 1) : d80225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5208, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8301 q ha hb
    | true =>
      simp only [d5208, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5209 q = 1) (hb : d77845 q = 1) : d80226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5209, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5209, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5210 q = 1) (hb : d77845 q = 1) : d80227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5210, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5210, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5211 q = 1) (hb : d77845 q = 1) : d80228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5211, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5211, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5212 q = 1) (hb : d77845 q = 1) : d80232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5212, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8302 q ha hb
    | true =>
      simp only [d5212, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5213 q = 1) (hb : d77845 q = 1) : d80233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5213, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5213, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5214 q = 1) (hb : d77845 q = 1) : d80234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5214, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5214, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5215 q = 1) (hb : d77845 q = 1) : d80239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8304 q ha hb
    | true =>
      simp only [d5215, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69673 q = 1) (hb : d77845 q = 1) : d80240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69673, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69673, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8295 q ha hb
    | true =>
      simp only [d2275, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d77845 q = 1) : d80241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69674 q = 1) (hb : d77845 q = 1) : d80242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69674, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69674, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69675 q = 1) (hb : d77845 q = 1) : d80243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69675, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69675, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69676 q = 1) (hb : d77845 q = 1) : d80244 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69676, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69676, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5222 q = 1) (hb : d77845 q = 1) : d80247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5222, d77845, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8306 q ha hb
    | true =>
      simp only [d5222, d77845, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d5223 q = 1) (hb : d77845 q = 1) : d80248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5223, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5223, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5224 q = 1) (hb : d77845 q = 1) : d80249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5224, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5224, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d5225 q = 1) (hb : d77845 q = 1) : d80250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5225, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5225, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5226 q = 1) (hb : d77845 q = 1) : d80252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5226, d77845, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8307 q ha hb
    | true =>
      simp only [d5226, d77845, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d5227 q = 1) (hb : d77845 q = 1) : d80253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5227, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5227, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5228 q = 1) (hb : d77845 q = 1) : d80254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5228, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5228, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5229 q = 1) (hb : d77845 q = 1) : d80256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8308 q ha hb
    | true =>
      simp only [d5229, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69678 q = 1) (hb : d77845 q = 1) : d80257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69678, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69678, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d2298 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8297 q ha hb
    | true =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d2299 q = 1) (hb : d77845 q = 1) : d80258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d2299, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69679 q = 1) (hb : d77845 q = 1) : d80259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69679, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69679, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69680 q = 1) (hb : d77845 q = 1) : d80260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69680, d80260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69680, d80260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69681 q = 1) (hb : d77845 q = 1) : d80261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69681, d80261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69681, d80261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69682 q = 1) (hb : d77845 q = 1) : d80262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69682, d80262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69682, d80262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8310 (p : Pattern) (ha : d69689 p = 1) (hb : d77845 p = 1) : d80269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5229 q = 1) (hb : d77845 q = 1) : d80256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8308 q ha hb
    | true =>
      simp only [d5229, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69678 q = 1) (hb : d77845 q = 1) : d80257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69678, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69678, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2298 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8297 q ha hb
    | true =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2299 q = 1) (hb : d77845 q = 1) : d80258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2299, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69679 q = 1) (hb : d77845 q = 1) : d80259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69679, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69679, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69687 q = 1) (hb : d77845 q = 1) : d80267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69687, d80267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69687, d80267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69688 q = 1) (hb : d77845 q = 1) : d80268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69688, d80268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69688, d80268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69689 q = 1) (hb : d77845 q = 1) : d80269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69689, d80269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69689, d80269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8311 (p : Pattern) (ha : d2377 p = 1) (hb : d77842 p = 1) : d8143 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2370 q = 1) : d2370 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2376 q = 1) (hb : d77842 q = 1) : d8142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d77842, d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2376, d77842, d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2377 q = 1) (hb : d77842 q = 1) : d8143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d8143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2377, d8143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8312 (p : Pattern) (ha : d2383 p = 1) (hb : d77844 p = 1) : d80278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2378 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8311 q ha hb
    | true =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2379 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2380 q = 1) (hb : d77844 q = 1) : d80275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2380, d77844, d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2380, d77844, d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2381 q = 1) (hb : d77844 q = 1) : d80276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2381, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2381, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2382 q = 1) (hb : d77844 q = 1) : d80277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2382, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2382, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2383 q = 1) (hb : d77844 q = 1) : d80278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2383, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2383, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8313 (p : Pattern) (ha : d2391 p = 1) (hb : d77844 p = 1) : d80284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2387 q = 1) (hb : d77842 q = 1) : d2387 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2388 q = 1) (hb : d77844 q = 1) : d80281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d77844, d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2388, d77844, d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2389 q = 1) (hb : d77844 q = 1) : d80282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2389, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2390 q = 1) (hb : d77844 q = 1) : d80283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2390, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d2391 q = 1) (hb : d77844 q = 1) : d80284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2391, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8314 (p : Pattern) (ha : d69699 p = 1) (hb : d77845 p = 1) : d80290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5283 q = 1) (hb : d77845 q = 1) : d80279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5283, d77845, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8312 q ha hb
    | true =>
      simp only [d5283, d77845, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69695 q = 1) (hb : d77845 q = 1) : d80280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69695, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69695, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2442 q = 1) (hb : d77845 q = 1) : d80285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d77845, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8313 q ha hb
    | true =>
      simp only [d2442, d77845, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2443 q = 1) (hb : d77845 q = 1) : d80286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d80286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2443, d80286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69696 q = 1) (hb : d77845 q = 1) : d80287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69696, d80287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69696, d80287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69697 q = 1) (hb : d77845 q = 1) : d80288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69697, d80288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69697, d80288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69698 q = 1) (hb : d77845 q = 1) : d80289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69698, d80289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69698, d80289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69699 q = 1) (hb : d77845 q = 1) : d80290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69699, d80290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69699, d80290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8315 (p : Pattern) (ha : d70089 p = 1) (hb : d77845 p = 1) : d80296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5198 q = 1) (hb : d77845 q = 1) : d80211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5198, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5198, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8296 q ha hb
  have h2 (q : Pattern) (ha : d5199 q = 1) (hb : d77845 q = 1) : d80212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5199, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5199, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5205 q = 1) (hb : d77845 q = 1) : d80220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8296 q ha hb
    | true =>
      simp only [d5205, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8298 q ha hb
  have h4 (q : Pattern) (ha : d5206 q = 1) (hb : d77845 q = 1) : d80221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5206, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5207 q = 1) (hb : d77845 q = 1) : d80222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5207, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5207, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69683 q = 1) (hb : d77845 q = 1) : d80263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69683, d80263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8305 q ha hb
    | true =>
      simp only [d69683, d80263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8309 q ha hb
  have h7 (q : Pattern) (ha : d5271 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8300 q ha hb
    | true =>
      simp only [d5271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8291 q ha hb
  have h8 (q : Pattern) (ha : d70078 q = 1) (hb : d77845 q = 1) : d80264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70078, d80264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70078, d80264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70079 q = 1) (hb : d77845 q = 1) : d80265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70079, d80265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70079, d80265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70080 q = 1) (hb : d77845 q = 1) : d80266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70080, d80266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70080, d80266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69690 q = 1) (hb : d77845 q = 1) : d80270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69690, d80270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69690, d80270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8310 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8292 q ha hb
  have h13 (q : Pattern) (ha : d70081 q = 1) (hb : d77845 q = 1) : d80271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70081, d80271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70081, d80271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70082 q = 1) (hb : d77845 q = 1) : d80272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70082, d80272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70082, d80272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70083 q = 1) (hb : d77845 q = 1) : d80273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70083, d80273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70083, d80273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70084 q = 1) (hb : d77845 q = 1) : d80274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70084, d80274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70084, d80274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69700 q = 1) (hb : d77845 q = 1) : d80291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69700, d80291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69700, d80291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8314 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8294 q ha hb
  have h19 (q : Pattern) (ha : d70085 q = 1) (hb : d77845 q = 1) : d80292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70085, d80292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70085, d80292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70086 q = 1) (hb : d77845 q = 1) : d80293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70086, d80293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70086, d80293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70087 q = 1) (hb : d77845 q = 1) : d80294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70087, d80294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70087, d80294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70088 q = 1) (hb : d77845 q = 1) : d80295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70088, d80295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70088, d80295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70089 q = 1) (hb : d77845 q = 1) : d80296 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70089, d80296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70089, d80296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8316 (p : Pattern) (ha : d70095 p = 1) (hb : d77845 p = 1) : d80302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70090 q = 1) (hb : d77845 q = 1) : d80297 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70090, d80297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70090, d80297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8315 q ha hb
  have h2 (q : Pattern) (ha : d70091 q = 1) (hb : d77845 q = 1) : d80298 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70091, d80298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70091, d80298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70092 q = 1) (hb : d77845 q = 1) : d80299 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70092, d80299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70092, d80299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70093 q = 1) (hb : d77845 q = 1) : d80300 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70093, d80300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70093, d80300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70094 q = 1) (hb : d77845 q = 1) : d80301 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70094, d80301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70094, d80301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70095 q = 1) (hb : d77845 q = 1) : d80302 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70095, d80302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70095, d80302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8317 (p : Pattern) (ha : d70101 p = 1) (hb : d77845 p = 1) : d80308 p = 1 := by
  have h0 (q : Pattern) (ha : d70014 q = 1) (hb : d77845 q = 1) : d79885 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70014, d79885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8176 q ha hb
    | true =>
      simp only [d70014, d79885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8204 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70033 q = 1) (hb : d77845 q = 1) : d79988 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70033, d79988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70033, d79988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8232 q ha hb
  have h3 (q : Pattern) (ha : d70034 q = 1) (hb : d77845 q = 1) : d79989 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70034, d79989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70034, d79989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70053 q = 1) (hb : d77845 q = 1) : d80092 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70053, d80092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70053, d80092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8260 q ha hb
  have h5 (q : Pattern) (ha : d70054 q = 1) (hb : d77845 q = 1) : d80093 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70054, d80093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70054, d80093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70055 q = 1) (hb : d77845 q = 1) : d80094 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70055, d80094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70055, d80094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70074 q = 1) (hb : d77845 q = 1) : d80197 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70074, d80197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70074, d80197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8288 q ha hb
  have h8 (q : Pattern) (ha : d70075 q = 1) (hb : d77845 q = 1) : d80198 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70075, d80198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70075, d80198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70076 q = 1) (hb : d77845 q = 1) : d80199 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70076, d80199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70076, d80199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70077 q = 1) (hb : d77845 q = 1) : d80200 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70077, d80200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70077, d80200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70096 q = 1) (hb : d77845 q = 1) : d80303 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70096, d80303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70096, d80303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8316 q ha hb
  have h12 (q : Pattern) (ha : d70097 q = 1) (hb : d77845 q = 1) : d80304 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70097, d80304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70097, d80304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70098 q = 1) (hb : d77845 q = 1) : d80305 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70098, d80305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70098, d80305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70099 q = 1) (hb : d77845 q = 1) : d80306 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70099, d80306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70099, d80306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70100 q = 1) (hb : d77845 q = 1) : d80307 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70100, d80307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70100, d80307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70101 q = 1) (hb : d77845 q = 1) : d80308 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70101, d80308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70101, d80308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8318 (p : Pattern) (ha : d70107 p = 1) (hb : d77845 p = 1) : d80314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70102 q = 1) (hb : d77845 q = 1) : d80309 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70102, d80309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8317 q ha hb
    | true =>
      simp only [d70102, d80309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70103 q = 1) (hb : d77845 q = 1) : d80310 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70103, d80310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70103, d80310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70104 q = 1) (hb : d77845 q = 1) : d80311 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70104, d80311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70104, d80311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70105 q = 1) (hb : d77845 q = 1) : d80312 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70105, d80312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70105, d80312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70106 q = 1) (hb : d77845 q = 1) : d80313 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70106, d80313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70106, d80313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70107 q = 1) (hb : d77845 q = 1) : d80314 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70107, d80314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70107, d80314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8319 (p : Pattern) (ha : d70113 p = 1) (hb : d77845 p = 1) : d80320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70108 q = 1) (hb : d77845 q = 1) : d80315 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70108, d80315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8318 q ha hb
    | true =>
      simp only [d70108, d80315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70109 q = 1) (hb : d77845 q = 1) : d80316 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70109, d80316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70109, d80316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70110 q = 1) (hb : d77845 q = 1) : d80317 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70110, d80317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70110, d80317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70111 q = 1) (hb : d77845 q = 1) : d80318 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70111, d80318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70111, d80318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70112 q = 1) (hb : d77845 q = 1) : d80319 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70112, d80319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70112, d80319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70113 q = 1) (hb : d77845 q = 1) : d80320 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70113, d80320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70113, d80320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8320 (p : Pattern) (ha : d70119 p = 1) (hb : d77845 p = 1) : d80326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70114 q = 1) (hb : d77845 q = 1) : d80321 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70114, d80321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8319 q ha hb
    | true =>
      simp only [d70114, d80321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70115 q = 1) (hb : d77845 q = 1) : d80322 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70115, d80322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70115, d80322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70116 q = 1) (hb : d77845 q = 1) : d80323 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70116, d80323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70116, d80323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70117 q = 1) (hb : d77845 q = 1) : d80324 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70117, d80324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70117, d80324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70118 q = 1) (hb : d77845 q = 1) : d80325 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70118, d80325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70118, d80325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70119 q = 1) (hb : d77845 q = 1) : d80326 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70119, d80326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70119, d80326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8321 (p : Pattern) (ha : d70125 p = 1) (hb : d77845 p = 1) : d80332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70120 q = 1) (hb : d77845 q = 1) : d80327 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70120, d80327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8320 q ha hb
    | true =>
      simp only [d70120, d80327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70121 q = 1) (hb : d77845 q = 1) : d80328 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70121, d80328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70121, d80328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70122 q = 1) (hb : d77845 q = 1) : d80329 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70122, d80329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70122, d80329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70123 q = 1) (hb : d77845 q = 1) : d80330 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70123, d80330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70123, d80330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70124 q = 1) (hb : d77845 q = 1) : d80331 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70124, d80331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70124, d80331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70125 q = 1) (hb : d77845 q = 1) : d80332 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70125, d80332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70125, d80332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8322 (p : Pattern) (ha : d70131 p = 1) (hb : d77845 p = 1) : d80338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70126 q = 1) (hb : d77845 q = 1) : d80333 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70126, d80333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8321 q ha hb
    | true =>
      simp only [d70126, d80333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70127 q = 1) (hb : d77845 q = 1) : d80334 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70127, d80334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70127, d80334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70128 q = 1) (hb : d77845 q = 1) : d80335 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70128, d80335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70128, d80335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70129 q = 1) (hb : d77845 q = 1) : d80336 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70129, d80336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70129, d80336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70130 q = 1) (hb : d77845 q = 1) : d80337 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70130, d80337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70130, d80337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70131 q = 1) (hb : d77845 q = 1) : d80338 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70131, d80338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70131, d80338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8323 (p : Pattern) (ha : d70137 p = 1) (hb : d77845 p = 1) : d80344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70132 q = 1) (hb : d77845 q = 1) : d80339 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70132, d80339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8322 q ha hb
    | true =>
      simp only [d70132, d80339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70133 q = 1) (hb : d77845 q = 1) : d80340 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70133, d80340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70133, d80340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70134 q = 1) (hb : d77845 q = 1) : d80341 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70134, d80341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70134, d80341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70135 q = 1) (hb : d77845 q = 1) : d80342 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70135, d80342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70135, d80342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70136 q = 1) (hb : d77845 q = 1) : d80343 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70136, d80343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70136, d80343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70137 q = 1) (hb : d77845 q = 1) : d80344 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70137, d80344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70137, d80344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8324 (p : Pattern) (ha : d70143 p = 1) (hb : d77845 p = 1) : d80350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70138 q = 1) (hb : d77845 q = 1) : d80345 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70138, d80345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8323 q ha hb
    | true =>
      simp only [d70138, d80345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d70139 q = 1) (hb : d77845 q = 1) : d80346 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70139, d80346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70139, d80346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d70140 q = 1) (hb : d77845 q = 1) : d80347 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70140, d80347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70140, d80347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d70141 q = 1) (hb : d77845 q = 1) : d80348 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70141, d80348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70141, d80348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d70142 q = 1) (hb : d77845 q = 1) : d80349 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70142, d80349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70142, d80349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d70143 q = 1) (hb : d77845 q = 1) : d80350 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70143, d80350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70143, d80350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8325 (p : Pattern) (ha : d36 p = 1) (hb : d78795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d35 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36 q = 1) (hb : d78795 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, d78795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36, d78795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8326 (p : Pattern) (ha : d78800 p = 1) (hb : d79651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78799 q = 1) (hb : d79650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78799, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78799, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78800 q = 1) (hb : d79651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78800, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78800, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8327 (p : Pattern) (ha : d78806 p = 1) (hb : d79657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78802 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78803 q = 1) (hb : d79654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78803, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78803, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78804 q = 1) (hb : d79655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78804, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78804, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78805 q = 1) (hb : d79656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78805, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78805, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78806 q = 1) (hb : d79657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78806, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78806, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8328 (p : Pattern) (ha : d78807 p = 1) (hb : d79658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78799 q = 1) (hb : d79650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78799, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78799, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d78807 q = 1) (hb : d79658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78807, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78807, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8329 (p : Pattern) (ha : d78813 p = 1) (hb : d79664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78802 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78803 q = 1) (hb : d79654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78803, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78803, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78804 q = 1) (hb : d79655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78804, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78804, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78805 q = 1) (hb : d79656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78805, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78805, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78809 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78810 q = 1) (hb : d79661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78810, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78810, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78811 q = 1) (hb : d79662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78811, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78811, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78812 q = 1) (hb : d79663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78812, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78812, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78813 q = 1) (hb : d79664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78813, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78813, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8330 (p : Pattern) (ha : d78818 p = 1) (hb : d79669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78809 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78810 q = 1) (hb : d79661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78810, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78810, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78811 q = 1) (hb : d79662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78811, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78811, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78812 q = 1) (hb : d79663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78812, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78812, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78818 q = 1) (hb : d79669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78818, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78818, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8331 (p : Pattern) (ha : d77 p = 1) (hb : d78824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77 q = 1) (hb : d78824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, d78824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77, d78824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8332 (p : Pattern) (ha : d78829 p = 1) (hb : d79678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78826 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78 q = 1) (hb : d78825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d78825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8331 q ha hb
    | true =>
      simp only [d78, d78825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d78826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d78826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79, d78826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78826 q = 1) (hb : d79675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78827 q = 1) (hb : d79676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78827, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78827, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78828 q = 1) (hb : d79677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78828, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78828, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d78829 q = 1) (hb : d79678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78829, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78829, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8333 (p : Pattern) (ha : d78835 p = 1) (hb : d79684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78830 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8332 q ha hb
    | true =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78831 q = 1) (hb : d79680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78831, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78831, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78832 q = 1) (hb : d79681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78832, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78832, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78833 q = 1) (hb : d79682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78833, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78833, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78834 q = 1) (hb : d79683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78834, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78834, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78835 q = 1) (hb : d79684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78835, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78835, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8334 (p : Pattern) (ha : d78841 p = 1) (hb : d79690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78814 q = 1) (hb : d79665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78814, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8327 q ha hb
    | true =>
      simp only [d78814, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8329 q ha hb
  have h2 (q : Pattern) (ha : d78815 q = 1) (hb : d79666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78815, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78815, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78816 q = 1) (hb : d79667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78816, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78816, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78817 q = 1) (hb : d79668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78817, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78817, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78819 q = 1) (hb : d79670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78819, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78819, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8330 q ha hb
  have h6 (q : Pattern) (ha : d78820 q = 1) (hb : d79671 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78820, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78820, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78821 q = 1) (hb : d79672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78821, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78821, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78822 q = 1) (hb : d79673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78822, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78822, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78823 q = 1) (hb : d79674 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78823, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78823, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78836 q = 1) (hb : d79685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78836, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78836, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8333 q ha hb
  have h11 (q : Pattern) (ha : d78837 q = 1) (hb : d79686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78837, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d78837, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d78838 q = 1) (hb : d79687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78838, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78838, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78839 q = 1) (hb : d79688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78839, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78839, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78840 q = 1) (hb : d79689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78840, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d78840, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d78841 q = 1) (hb : d79690 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d78841, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78841, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8335 (p : Pattern) (ha : d78851 p = 1) (hb : d79700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78847 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78847, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78847, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78848 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78848, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78848, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78849 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78849, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78849, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78850 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78850, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78850, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78851 q = 1) (hb : d79700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78851, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78851, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8336 (p : Pattern) (ha : d78858 p = 1) (hb : d79707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78847 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78847, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78847, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78848 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78848, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78848, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78849 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78849, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78849, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78850 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78850, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78850, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78854 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78854, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78854, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78855 q = 1) (hb : d79704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78855, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78855, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78856 q = 1) (hb : d79705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78856, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78856, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78857 q = 1) (hb : d79706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78857, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78857, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78858 q = 1) (hb : d79707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78858, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78858, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8337 (p : Pattern) (ha : d78863 p = 1) (hb : d79712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78862 q = 1) (hb : d79711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78862, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78862, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78863 q = 1) (hb : d79712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78863, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78863, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8338 (p : Pattern) (ha : d78870 p = 1) (hb : d79719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78868 q = 1) (hb : d79717 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78868, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78868, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78869 q = 1) (hb : d79718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78869, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78869, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78870 q = 1) (hb : d79719 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78870, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78870, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8339 (p : Pattern) (ha : d7241 p = 1) (hb : d78874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7240 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7241 q = 1) (hb : d78874 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d78874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7241, d78874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8340 (p : Pattern) (ha : d78879 p = 1) (hb : d79726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7242 q = 1) (hb : d78875 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d78875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8339 q ha hb
    | true =>
      simp only [d7242, d78875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7243 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d78876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d78876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78876 q = 1) (hb : d79723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78877 q = 1) (hb : d79724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78877, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78877, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78878 q = 1) (hb : d79725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78878, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78878, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78879 q = 1) (hb : d79726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78879, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78879, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8341 (p : Pattern) (ha : d78885 p = 1) (hb : d79732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78864 q = 1) (hb : d79713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78864, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8337 q ha hb
    | true =>
      simp only [d78864, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78865 q = 1) (hb : d79714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78865, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78865, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78866 q = 1) (hb : d79715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78866, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78866, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78867 q = 1) (hb : d79716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78867, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78867, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78871 q = 1) (hb : d79720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78871, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8338 q ha hb
    | true =>
      simp only [d78871, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78872 q = 1) (hb : d79721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78872, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78872, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78873 q = 1) (hb : d79722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78873, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78873, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d78800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d78880 q = 1) (hb : d79727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78880, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8340 q ha hb
    | true =>
      simp only [d78880, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d78881 q = 1) (hb : d79728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78802 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78882 q = 1) (hb : d79729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78882, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78882, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78883 q = 1) (hb : d79730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78883, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78883, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d78884 q = 1) (hb : d79731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78884, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78884, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78885 q = 1) (hb : d79732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78885, d79732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78885, d79732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8342 (p : Pattern) (ha : d78886 p = 1) (hb : d79733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78862 q = 1) (hb : d79711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78862, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78862, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78886 q = 1) (hb : d79733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78886, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78886, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8343 (p : Pattern) (ha : d78891 p = 1) (hb : d79738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d78796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8325 q ha hb
    | true =>
      simp only [d37, d78796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d78797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78868 q = 1) (hb : d79717 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78868, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78868, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78869 q = 1) (hb : d79718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78869, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78869, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78891 q = 1) (hb : d79738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78891, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78891, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8344 (p : Pattern) (ha : d78895 p = 1) (hb : d79742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7242 q = 1) (hb : d78875 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d78875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8339 q ha hb
    | true =>
      simp only [d7242, d78875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7243 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d78876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7243, d78876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78876 q = 1) (hb : d79723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78877 q = 1) (hb : d79724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78877, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78877, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78878 q = 1) (hb : d79725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78878, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78878, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d78895 q = 1) (hb : d79742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78895, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78895, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8345 (p : Pattern) (ha : d78901 p = 1) (hb : d79748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78864 q = 1) (hb : d79713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78864, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8337 q ha hb
    | true =>
      simp only [d78864, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78865 q = 1) (hb : d79714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78865, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78865, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78866 q = 1) (hb : d79715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78866, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78866, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78867 q = 1) (hb : d79716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78867, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78867, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78871 q = 1) (hb : d79720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78871, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8338 q ha hb
    | true =>
      simp only [d78871, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78872 q = 1) (hb : d79721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78872, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78872, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78873 q = 1) (hb : d79722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78873, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78873, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d78800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d78880 q = 1) (hb : d79727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78880, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8340 q ha hb
    | true =>
      simp only [d78880, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d78881 q = 1) (hb : d79728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d78801 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8326 q ha hb
    | true =>
      simp only [d78801, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78802 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78802, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78882 q = 1) (hb : d79729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78882, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78882, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78883 q = 1) (hb : d79730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78883, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78883, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d78884 q = 1) (hb : d79731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78884, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78884, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78887 q = 1) (hb : d79734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78887, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8342 q ha hb
    | true =>
      simp only [d78887, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d78888 q = 1) (hb : d79735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78888, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78888, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d78889 q = 1) (hb : d79736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78889, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d78889, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d78890 q = 1) (hb : d79737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78890, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78890, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d78892 q = 1) (hb : d79739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78892, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8343 q ha hb
    | true =>
      simp only [d78892, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d78893 q = 1) (hb : d79740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78893, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78893, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d78894 q = 1) (hb : d79741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78894, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d78894, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d78807 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d78896 q = 1) (hb : d79743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78896, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8344 q ha hb
    | true =>
      simp only [d78896, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d78808 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d78897 q = 1) (hb : d79744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d78897, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d78809 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d78898 q = 1) (hb : d79745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78898, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d78898, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d78899 q = 1) (hb : d79746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78899, d79746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d78899, d79746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d78900 q = 1) (hb : d79747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78900, d79747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d78900, d79747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d78901 q = 1) (hb : d79748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78901, d79748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d78901, d79748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8346 (p : Pattern) (ha : d78910 p = 1) (hb : d79755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78807 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78896 q = 1) (hb : d79743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78896, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8344 q ha hb
    | true =>
      simp only [d78896, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78808 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78897 q = 1) (hb : d79744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78897, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78808 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8328 q ha hb
    | true =>
      simp only [d78808, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78809 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78809, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78898 q = 1) (hb : d79745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78898, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78898, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78908 q = 1) (hb : d79753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78908, d79753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78908, d79753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78909 q = 1) (hb : d79754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78909, d79754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78909, d79754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78910 q = 1) (hb : d79755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78910, d79755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78910, d79755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8347 (p : Pattern) (ha : d7274 p = 1) (hb : d78916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7273 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7274 q = 1) (hb : d78916 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d78916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7274, d78916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8348 (p : Pattern) (ha : d78921 p = 1) (hb : d79764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7275 q = 1) (hb : d78917 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d78917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8347 q ha hb
    | true =>
      simp only [d7275, d78917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7276 q = 1) (hb : d78918 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d78918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7276, d78918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78918 q = 1) (hb : d79761 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78919 q = 1) (hb : d79762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78919, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78919, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78920 q = 1) (hb : d79763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78920, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78920, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d78921 q = 1) (hb : d79764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78921, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78921, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8349 (p : Pattern) (ha : d78927 p = 1) (hb : d79770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78922 q = 1) (hb : d79765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78922, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8348 q ha hb
    | true =>
      simp only [d78922, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78923 q = 1) (hb : d79766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78923, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78923, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78830 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8332 q ha hb
    | true =>
      simp only [d78830, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78831 q = 1) (hb : d79680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78831, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78831, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78924 q = 1) (hb : d79767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78924, d79767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78924, d79767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78925 q = 1) (hb : d79768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78925, d79768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78925, d79768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78926 q = 1) (hb : d79769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78926, d79769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78926, d79769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78927 q = 1) (hb : d79770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78927, d79770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78927, d79770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8350 (p : Pattern) (ha : d78933 p = 1) (hb : d79776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78852 q = 1) (hb : d79701 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78852, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78852, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8335 q ha hb
  have h2 (q : Pattern) (ha : d78853 q = 1) (hb : d79702 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78853, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78853, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78859 q = 1) (hb : d79708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78859, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8335 q ha hb
    | true =>
      simp only [d78859, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8336 q ha hb
  have h4 (q : Pattern) (ha : d78860 q = 1) (hb : d79709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78860, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78860, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78861 q = 1) (hb : d79710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78861, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78861, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78902 q = 1) (hb : d79749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78902, d79749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8341 q ha hb
    | true =>
      simp only [d78902, d79749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8345 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d78904 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d78905 q = 1) (hb : d79750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78905, d79750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78905, d79750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d78906 q = 1) (hb : d79751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78906, d79751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d78906, d79751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d78907 q = 1) (hb : d79752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78907, d79752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78907, d79752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78911 q = 1) (hb : d79756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78911, d79756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78911, d79756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8346 q ha hb
  have h12 (q : Pattern) (ha : d78912 q = 1) (hb : d79757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78912, d79757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78912, d79757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78913 q = 1) (hb : d79758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78913, d79758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78913, d79758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78914 q = 1) (hb : d79759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78914, d79759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d78914, d79759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d78915 q = 1) (hb : d79760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78915, d79760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d78915, d79760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d78928 q = 1) (hb : d79771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78928, d79771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78928, d79771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8349 q ha hb
  have h17 (q : Pattern) (ha : d78929 q = 1) (hb : d79772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78929, d79772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d78929, d79772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d78930 q = 1) (hb : d79773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78930, d79773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d78930, d79773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d78931 q = 1) (hb : d79774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78931, d79774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d78931, d79774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d78932 q = 1) (hb : d79775 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78932, d79775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d78932, d79775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d78933 q = 1) (hb : d79776 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d78933, d79776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d78933, d79776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8351 (p : Pattern) (ha : d78939 p = 1) (hb : d79782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78842 q = 1) (hb : d79691 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d78842, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78842, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8334 q ha hb
  have h2 (q : Pattern) (ha : d78843 q = 1) (hb : d79692 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d78843, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78843, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78844 q = 1) (hb : d79693 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d78844, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78844, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78845 q = 1) (hb : d79694 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d78845, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78845, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78846 q = 1) (hb : d79695 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d78846, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78846, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78934 q = 1) (hb : d79777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d78934, d79777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78934, d79777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8350 q ha hb
  have h7 (q : Pattern) (ha : d78935 q = 1) (hb : d79778 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d78935, d79778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78935, d79778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78936 q = 1) (hb : d79779 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d78936, d79779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78936, d79779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d78937 q = 1) (hb : d79780 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d78937, d79780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78937, d79780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78938 q = 1) (hb : d79781 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d78938, d79781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78938, d79781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78939 q = 1) (hb : d79782 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d78939, d79782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78939, d79782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8352 (p : Pattern) (ha : d481 p = 1) (hb : d78940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d78940 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d78940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d78940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8353 (p : Pattern) (ha : d78945 p = 1) (hb : d79786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78944 q = 1) (hb : d79785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78944, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78944, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78945 q = 1) (hb : d79786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78945, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78945, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8354 (p : Pattern) (ha : d78951 p = 1) (hb : d79792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78947 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78947, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78947, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78948 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78948, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78948, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78949 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78949, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78949, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78950 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78950, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78950, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78951 q = 1) (hb : d79792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78951, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78951, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8355 (p : Pattern) (ha : d78954 p = 1) (hb : d79795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78944 q = 1) (hb : d79785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78944, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78944, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d78954 q = 1) (hb : d79795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78954, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78954, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8356 (p : Pattern) (ha : d78960 p = 1) (hb : d79801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78947 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78947, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78947, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78948 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78948, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78948, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78949 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78949, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78949, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78950 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78950, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78950, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78955 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8355 q ha hb
    | true =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78956 q = 1) (hb : d79797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78956, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78956, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78957 q = 1) (hb : d79798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78957, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78957, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78958 q = 1) (hb : d79799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78958, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78958, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78959 q = 1) (hb : d79800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78959, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78959, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78960 q = 1) (hb : d79801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78960, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78960, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8357 (p : Pattern) (ha : d78965 p = 1) (hb : d79806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78964 q = 1) (hb : d79805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78964, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78964, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78965 q = 1) (hb : d79806 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78965, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78965, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8358 (p : Pattern) (ha : d78972 p = 1) (hb : d79813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78970 q = 1) (hb : d79811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78970, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78970, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78971 q = 1) (hb : d79812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78971, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78971, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78972 q = 1) (hb : d79813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78972, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78972, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8359 (p : Pattern) (ha : d7326 p = 1) (hb : d78976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d328 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7325 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7326 q = 1) (hb : d78976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d78976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7326, d78976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8360 (p : Pattern) (ha : d78981 p = 1) (hb : d79820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7327 q = 1) (hb : d78977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d78977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8359 q ha hb
    | true =>
      simp only [d7327, d78977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7328 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d78978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d78978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78978 q = 1) (hb : d79817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78979 q = 1) (hb : d79818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78979, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78979, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78980 q = 1) (hb : d79819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78980, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78980, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78981 q = 1) (hb : d79820 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78981, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78981, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8361 (p : Pattern) (ha : d78994 p = 1) (hb : d79827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78966 q = 1) (hb : d79807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78966, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8357 q ha hb
    | true =>
      simp only [d78966, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78967 q = 1) (hb : d79808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78967, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78967, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78968 q = 1) (hb : d79809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78968, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78968, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78969 q = 1) (hb : d79810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78969, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78969, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78973 q = 1) (hb : d79814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78973, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8358 q ha hb
    | true =>
      simp only [d78973, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78974 q = 1) (hb : d79815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78974, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78974, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78975 q = 1) (hb : d79816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78975, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78975, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d78987 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d78988 q = 1) (hb : d79821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78988, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8360 q ha hb
    | true =>
      simp only [d78988, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78946 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d78989 q = 1) (hb : d79822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78989, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78989, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78990 q = 1) (hb : d79823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78990, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78990, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78991 q = 1) (hb : d79824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78991, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78991, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78992 q = 1) (hb : d79825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78992, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78992, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d78993 q = 1) (hb : d79826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78993, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78993, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78994 q = 1) (hb : d79827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78994, d79827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78994, d79827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8362 (p : Pattern) (ha : d78995 p = 1) (hb : d79828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78964 q = 1) (hb : d79805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78964, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78964, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78995 q = 1) (hb : d79828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78995, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78995, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8363 (p : Pattern) (ha : d79000 p = 1) (hb : d79833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d78941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8352 q ha hb
    | true =>
      simp only [d482, d78941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d78942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78970 q = 1) (hb : d79811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78970, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78970, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78971 q = 1) (hb : d79812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78971, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78971, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79000 q = 1) (hb : d79833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79000, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79000, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8364 (p : Pattern) (ha : d79004 p = 1) (hb : d79837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7327 q = 1) (hb : d78977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d78977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8359 q ha hb
    | true =>
      simp only [d7327, d78977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7328 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d78978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7328, d78978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78978 q = 1) (hb : d79817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78979 q = 1) (hb : d79818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78979, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78979, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d78980 q = 1) (hb : d79819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78980, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78980, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79004 q = 1) (hb : d79837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79004, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79004, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8365 (p : Pattern) (ha : d79012 p = 1) (hb : d79844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78966 q = 1) (hb : d79807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78966, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8357 q ha hb
    | true =>
      simp only [d78966, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78967 q = 1) (hb : d79808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78967, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78967, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78968 q = 1) (hb : d79809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78968, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78968, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78969 q = 1) (hb : d79810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78969, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78969, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78973 q = 1) (hb : d79814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78973, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8358 q ha hb
    | true =>
      simp only [d78973, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78974 q = 1) (hb : d79815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78974, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78974, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78975 q = 1) (hb : d79816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78975, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78975, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d78987 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d78988 q = 1) (hb : d79821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78988, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8360 q ha hb
    | true =>
      simp only [d78988, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78946 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d78989 q = 1) (hb : d79822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78989, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78989, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d78946 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8353 q ha hb
    | true =>
      simp only [d78946, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78990 q = 1) (hb : d79823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78990, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78990, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78991 q = 1) (hb : d79824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78991, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78991, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78992 q = 1) (hb : d79825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78992, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78992, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d78993 q = 1) (hb : d79826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78993, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78993, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78996 q = 1) (hb : d79829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78996, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8362 q ha hb
    | true =>
      simp only [d78996, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d78997 q = 1) (hb : d79830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78997, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78997, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d78998 q = 1) (hb : d79831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78998, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d78998, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d78999 q = 1) (hb : d79832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78999, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78999, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79001 q = 1) (hb : d79834 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79001, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8363 q ha hb
    | true =>
      simp only [d79001, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d79002 q = 1) (hb : d79835 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79002, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79002, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d79003 q = 1) (hb : d79836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79003, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d79003, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d79005 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d79006 q = 1) (hb : d79838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79006, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8364 q ha hb
    | true =>
      simp only [d79006, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d78955 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79007 q = 1) (hb : d79839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79007, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d79007, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d78955 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8355 q ha hb
    | true =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d79008 q = 1) (hb : d79840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79008, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d79008, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d79009 q = 1) (hb : d79841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79009, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79009, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d79010 q = 1) (hb : d79842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79010, d79842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d79010, d79842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d79011 q = 1) (hb : d79843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79011, d79843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79011, d79843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d79012 q = 1) (hb : d79844 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79012, d79844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79012, d79844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8366 (p : Pattern) (ha : d79026 p = 1) (hb : d79851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79006 q = 1) (hb : d79838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79006, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8364 q ha hb
    | true =>
      simp only [d79006, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79007 q = 1) (hb : d79839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79007, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79007, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78955 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8355 q ha hb
    | true =>
      simp only [d78955, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79008 q = 1) (hb : d79840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79008, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79008, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79009 q = 1) (hb : d79841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79009, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79009, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79024 q = 1) (hb : d79849 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79024, d79849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79024, d79849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79025 q = 1) (hb : d79850 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79025, d79850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79025, d79850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79026 q = 1) (hb : d79851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79026, d79851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79026, d79851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8367 (p : Pattern) (ha : d7390 p = 1) (hb : d79032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7389 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7390 q = 1) (hb : d79032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d79032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7390, d79032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8368 (p : Pattern) (ha : d79037 p = 1) (hb : d79860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7391 q = 1) (hb : d79033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d79033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8367 q ha hb
    | true =>
      simp only [d7391, d79033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7392 q = 1) (hb : d79034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d79034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7392, d79034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79034 q = 1) (hb : d79857 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79035 q = 1) (hb : d79858 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79035, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79035, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79036 q = 1) (hb : d79859 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79036, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79036, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79037 q = 1) (hb : d79860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79037, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79037, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8369 (p : Pattern) (ha : d683 p = 1) (hb : d79045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d79045 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d79045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d79045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8370 (p : Pattern) (ha : d79050 p = 1) (hb : d79866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79047 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d684 q = 1) (hb : d79046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d79046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8369 q ha hb
    | true =>
      simp only [d684, d79046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d79047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d79047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d685, d79047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79047 q = 1) (hb : d79863 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79048 q = 1) (hb : d79864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79048, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79048, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79049 q = 1) (hb : d79865 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79049, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79049, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79050 q = 1) (hb : d79866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79050, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79050, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8371 (p : Pattern) (ha : d79057 p = 1) (hb : d79872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79044 q = 1) (hb : d79861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79044, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8368 q ha hb
    | true =>
      simp only [d79044, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79052 q = 1) (hb : d79862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79052, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79052, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79051 q = 1) (hb : d79867 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79051, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8370 q ha hb
    | true =>
      simp only [d79051, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79053 q = 1) (hb : d79868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79053, d79868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79053, d79868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79054 q = 1) (hb : d79869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79054, d79869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79054, d79869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79055 q = 1) (hb : d79870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79055, d79870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79055, d79870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79056 q = 1) (hb : d79871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79056, d79871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79056, d79871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79057 q = 1) (hb : d79872 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79057, d79872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79057, d79872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8372 (p : Pattern) (ha : d79063 p = 1) (hb : d79878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78952 q = 1) (hb : d79793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78952, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78952, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8354 q ha hb
  have h2 (q : Pattern) (ha : d78953 q = 1) (hb : d79794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78953, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78953, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78961 q = 1) (hb : d79802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78961, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8354 q ha hb
    | true =>
      simp only [d78961, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8356 q ha hb
  have h4 (q : Pattern) (ha : d78962 q = 1) (hb : d79803 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78962, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78962, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78963 q = 1) (hb : d79804 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78963, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78963, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79013 q = 1) (hb : d79845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79013, d79845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8361 q ha hb
    | true =>
      simp only [d79013, d79845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8365 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d79020 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d79021 q = 1) (hb : d79846 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79021, d79846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79021, d79846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d79022 q = 1) (hb : d79847 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79022, d79847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79022, d79847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d79023 q = 1) (hb : d79848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79023, d79848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79023, d79848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79027 q = 1) (hb : d79852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79027, d79852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79027, d79852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8366 q ha hb
  have h12 (q : Pattern) (ha : d79028 q = 1) (hb : d79853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79028, d79853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79028, d79853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79029 q = 1) (hb : d79854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79029, d79854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79029, d79854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79030 q = 1) (hb : d79855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79030, d79855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79030, d79855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d79031 q = 1) (hb : d79856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79031, d79856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79031, d79856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79058 q = 1) (hb : d79873 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79058, d79873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79058, d79873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8371 q ha hb
  have h17 (q : Pattern) (ha : d79059 q = 1) (hb : d79874 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79059, d79874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79059, d79874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79060 q = 1) (hb : d79875 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79060, d79875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d79060, d79875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d79061 q = 1) (hb : d79876 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79061, d79876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79061, d79876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79062 q = 1) (hb : d79877 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79062, d79877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d79062, d79877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d79063 q = 1) (hb : d79878 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79063, d79878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79063, d79878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8373 (p : Pattern) (ha : d79069 p = 1) (hb : d79884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79064 q = 1) (hb : d79879 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79064, d79879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79064, d79879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8372 q ha hb
  have h2 (q : Pattern) (ha : d79065 q = 1) (hb : d79880 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79065, d79880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79065, d79880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79066 q = 1) (hb : d79881 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79066, d79881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79066, d79881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79067 q = 1) (hb : d79882 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79067, d79882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79067, d79882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79068 q = 1) (hb : d79883 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79068, d79883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79068, d79883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79069 q = 1) (hb : d79884 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79069, d79884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79069, d79884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8374 (p : Pattern) (ha : d773 p = 1) (hb : d79071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d772 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d773 q = 1) (hb : d79071 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d79071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d773, d79071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8375 (p : Pattern) (ha : d79076 p = 1) (hb : d79889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79075 q = 1) (hb : d79888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79075, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79075, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79076 q = 1) (hb : d79889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79076, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79076, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8376 (p : Pattern) (ha : d79082 p = 1) (hb : d79895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79078 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79078, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79078, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79079 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79079, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79079, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79080 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79080, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79080, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79081 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79081, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79081, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79082 q = 1) (hb : d79895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79082, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79082, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8377 (p : Pattern) (ha : d79085 p = 1) (hb : d79898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79075 q = 1) (hb : d79888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79075, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79075, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79085 q = 1) (hb : d79898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79085, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79085, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8378 (p : Pattern) (ha : d79091 p = 1) (hb : d79904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79078 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79078, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79078, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79079 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79079, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79079, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79080 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79080, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79080, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79081 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79081, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79081, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79086 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8377 q ha hb
    | true =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79087 q = 1) (hb : d79900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79087, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79087, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79088 q = 1) (hb : d79901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79088, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79088, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79089 q = 1) (hb : d79902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79089, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79089, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79090 q = 1) (hb : d79903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79090, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79090, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79091 q = 1) (hb : d79904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79091, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79091, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8379 (p : Pattern) (ha : d79096 p = 1) (hb : d79909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79095 q = 1) (hb : d79908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79095, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79095, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79096 q = 1) (hb : d79909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79096, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79096, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8380 (p : Pattern) (ha : d79103 p = 1) (hb : d79916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79101 q = 1) (hb : d79914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79101, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79101, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79102 q = 1) (hb : d79915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79102, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79102, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79103 q = 1) (hb : d79916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79103, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79103, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8381 (p : Pattern) (ha : d7575 p = 1) (hb : d79107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d766 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d766, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7574 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7575 q = 1) (hb : d79107 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, d79107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7575, d79107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8382 (p : Pattern) (ha : d79112 p = 1) (hb : d79923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7576 q = 1) (hb : d79108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d79108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8381 q ha hb
    | true =>
      simp only [d7576, d79108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7577 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d79109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d79109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79109 q = 1) (hb : d79920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79110 q = 1) (hb : d79921 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79110, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79110, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79111 q = 1) (hb : d79922 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79111, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79111, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79112 q = 1) (hb : d79923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79112, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79112, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8383 (p : Pattern) (ha : d79125 p = 1) (hb : d79930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79097 q = 1) (hb : d79910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79097, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8379 q ha hb
    | true =>
      simp only [d79097, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79098 q = 1) (hb : d79911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79098, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79098, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79099 q = 1) (hb : d79912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79099, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79099, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79100 q = 1) (hb : d79913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79100, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79100, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79104 q = 1) (hb : d79917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79104, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8380 q ha hb
    | true =>
      simp only [d79104, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79105 q = 1) (hb : d79918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79105, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79105, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79106 q = 1) (hb : d79919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79106, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79106, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79118 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79119 q = 1) (hb : d79924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79119, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8382 q ha hb
    | true =>
      simp only [d79119, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79120 q = 1) (hb : d79925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79120, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79120, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79121 q = 1) (hb : d79926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79121, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79121, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79122 q = 1) (hb : d79927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79122, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79122, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79123 q = 1) (hb : d79928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79123, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79123, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79124 q = 1) (hb : d79929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79124, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79124, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79125 q = 1) (hb : d79930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79125, d79930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79125, d79930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8384 (p : Pattern) (ha : d79126 p = 1) (hb : d79931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79095 q = 1) (hb : d79908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79095, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79095, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79126 q = 1) (hb : d79931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79126, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79126, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8385 (p : Pattern) (ha : d79131 p = 1) (hb : d79936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d79072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8374 q ha hb
    | true =>
      simp only [d774, d79072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d79073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79101 q = 1) (hb : d79914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79101, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79101, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79102 q = 1) (hb : d79915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79102, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79102, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79131 q = 1) (hb : d79936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79131, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79131, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8386 (p : Pattern) (ha : d79135 p = 1) (hb : d79940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7576 q = 1) (hb : d79108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d79108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8381 q ha hb
    | true =>
      simp only [d7576, d79108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7577 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d79109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7577, d79109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79109 q = 1) (hb : d79920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79110 q = 1) (hb : d79921 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79110, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79110, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79111 q = 1) (hb : d79922 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79111, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79111, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79135 q = 1) (hb : d79940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79135, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79135, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8387 (p : Pattern) (ha : d79143 p = 1) (hb : d79947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79097 q = 1) (hb : d79910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79097, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8379 q ha hb
    | true =>
      simp only [d79097, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79098 q = 1) (hb : d79911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79098, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79098, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79099 q = 1) (hb : d79912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79099, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79099, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79100 q = 1) (hb : d79913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79100, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79100, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79104 q = 1) (hb : d79917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79104, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8380 q ha hb
    | true =>
      simp only [d79104, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79105 q = 1) (hb : d79918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79105, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79105, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79106 q = 1) (hb : d79919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79106, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79106, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79118 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79119 q = 1) (hb : d79924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79119, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8382 q ha hb
    | true =>
      simp only [d79119, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79120 q = 1) (hb : d79925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79120, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79120, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79077 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8375 q ha hb
    | true =>
      simp only [d79077, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79121 q = 1) (hb : d79926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79121, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79121, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79122 q = 1) (hb : d79927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79122, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79122, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79123 q = 1) (hb : d79928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79123, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79123, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79124 q = 1) (hb : d79929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79124, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79124, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79127 q = 1) (hb : d79932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79127, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8384 q ha hb
    | true =>
      simp only [d79127, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79128 q = 1) (hb : d79933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79128, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79128, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79129 q = 1) (hb : d79934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79129, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79129, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79130 q = 1) (hb : d79935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79130, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79130, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79132 q = 1) (hb : d79937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79132, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8385 q ha hb
    | true =>
      simp only [d79132, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d79133 q = 1) (hb : d79938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79133, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79133, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d79134 q = 1) (hb : d79939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79134, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d79134, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d79136 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d79137 q = 1) (hb : d79941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79137, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8386 q ha hb
    | true =>
      simp only [d79137, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d79086 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79138 q = 1) (hb : d79942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79138, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d79138, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d79086 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8377 q ha hb
    | true =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d79139 q = 1) (hb : d79943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79139, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d79139, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d79140 q = 1) (hb : d79944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79140, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79140, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d79141 q = 1) (hb : d79945 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79141, d79945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d79141, d79945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d79142 q = 1) (hb : d79946 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79142, d79946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79142, d79946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d79143 q = 1) (hb : d79947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79143, d79947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79143, d79947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8388 (p : Pattern) (ha : d79157 p = 1) (hb : d79954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79137 q = 1) (hb : d79941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79137, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8386 q ha hb
    | true =>
      simp only [d79137, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79086 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79138 q = 1) (hb : d79942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79138, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79138, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79086 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8377 q ha hb
    | true =>
      simp only [d79086, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79139 q = 1) (hb : d79943 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79139, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79139, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79140 q = 1) (hb : d79944 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79140, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79140, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79155 q = 1) (hb : d79952 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79155, d79952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79155, d79952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79156 q = 1) (hb : d79953 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79156, d79953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79156, d79953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79157 q = 1) (hb : d79954 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79157, d79954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79157, d79954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8389 (p : Pattern) (ha : d7681 p = 1) (hb : d79163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d990 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7680 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7681 q = 1) (hb : d79163 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, d79163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7681, d79163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8390 (p : Pattern) (ha : d79168 p = 1) (hb : d79963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79165 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7682 q = 1) (hb : d79164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d79164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8389 q ha hb
    | true =>
      simp only [d7682, d79164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7683 q = 1) (hb : d79165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d79165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7683, d79165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79165 q = 1) (hb : d79960 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79166 q = 1) (hb : d79961 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79166, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79166, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79167 q = 1) (hb : d79962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79167, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79167, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79168 q = 1) (hb : d79963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79168, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79168, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8391 (p : Pattern) (ha : d1005 p = 1) (hb : d79176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1005 q = 1) (hb : d79176 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d79176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1005, d79176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8392 (p : Pattern) (ha : d79181 p = 1) (hb : d79969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1006 q = 1) (hb : d79177 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d79177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8391 q ha hb
    | true =>
      simp only [d1006, d79177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d79178 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d79178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1007, d79178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79178 q = 1) (hb : d79966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79179 q = 1) (hb : d79967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79179, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79179, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79180 q = 1) (hb : d79968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79180, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79180, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79181 q = 1) (hb : d79969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79181, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79181, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8393 (p : Pattern) (ha : d79188 p = 1) (hb : d79975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79175 q = 1) (hb : d79964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79175, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8390 q ha hb
    | true =>
      simp only [d79175, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79182 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79183 q = 1) (hb : d79965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79183, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79183, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79182 q = 1) (hb : d79970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79182, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8392 q ha hb
    | true =>
      simp only [d79182, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79184 q = 1) (hb : d79971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79184, d79971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79184, d79971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79185 q = 1) (hb : d79972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79185, d79972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79185, d79972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79186 q = 1) (hb : d79973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79186, d79973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79186, d79973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79187 q = 1) (hb : d79974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79187, d79974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79187, d79974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79188 q = 1) (hb : d79975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79188, d79975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79188, d79975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8394 (p : Pattern) (ha : d79194 p = 1) (hb : d79981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79083 q = 1) (hb : d79896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79083, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79083, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8376 q ha hb
  have h2 (q : Pattern) (ha : d79084 q = 1) (hb : d79897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79084, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79084, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79092 q = 1) (hb : d79905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79092, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8376 q ha hb
    | true =>
      simp only [d79092, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8378 q ha hb
  have h4 (q : Pattern) (ha : d79093 q = 1) (hb : d79906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79093, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79093, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79094 q = 1) (hb : d79907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79094, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79094, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79144 q = 1) (hb : d79948 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79144, d79948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8383 q ha hb
    | true =>
      simp only [d79144, d79948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8387 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d79151 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d79152 q = 1) (hb : d79949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79152, d79949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79152, d79949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d79153 q = 1) (hb : d79950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79153, d79950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79153, d79950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d79154 q = 1) (hb : d79951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79154, d79951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79154, d79951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79158 q = 1) (hb : d79955 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79158, d79955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79158, d79955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8388 q ha hb
  have h12 (q : Pattern) (ha : d79159 q = 1) (hb : d79956 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79159, d79956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79159, d79956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79160 q = 1) (hb : d79957 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79160, d79957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79160, d79957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79161 q = 1) (hb : d79958 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79161, d79958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79161, d79958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d79162 q = 1) (hb : d79959 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79162, d79959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79162, d79959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79189 q = 1) (hb : d79976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79189, d79976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79189, d79976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8393 q ha hb
  have h17 (q : Pattern) (ha : d79190 q = 1) (hb : d79977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79190, d79977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79190, d79977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79191 q = 1) (hb : d79978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79191, d79978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d79191, d79978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d79192 q = 1) (hb : d79979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79192, d79979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79192, d79979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79193 q = 1) (hb : d79980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79193, d79980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d79193, d79980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d79194 q = 1) (hb : d79981 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79194, d79981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79194, d79981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8395 (p : Pattern) (ha : d79200 p = 1) (hb : d79987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79195 q = 1) (hb : d79982 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79195, d79982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79195, d79982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8394 q ha hb
  have h2 (q : Pattern) (ha : d79196 q = 1) (hb : d79983 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79196, d79983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79196, d79983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79197 q = 1) (hb : d79984 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79197, d79984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79197, d79984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79198 q = 1) (hb : d79985 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79198, d79985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79198, d79985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79199 q = 1) (hb : d79986 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79199, d79986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79199, d79986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79200 q = 1) (hb : d79987 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79200, d79987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79200, d79987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8396 (p : Pattern) (ha : d1152 p = 1) (hb : d79203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1142 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro155 q ha hb
  have h2 (q : Pattern) (ha : d1143 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1144 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1146 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1151 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1152 q = 1) (hb : d79203 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d79203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1152, d79203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8397 (p : Pattern) (ha : d79208 p = 1) (hb : d79993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79207 q = 1) (hb : d79992 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79207, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79207, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79208 q = 1) (hb : d79993 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79208, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79208, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8398 (p : Pattern) (ha : d79214 p = 1) (hb : d79999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79210 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79210, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79210, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79211 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79211, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79211, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79212 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79212, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79212, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79213 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79213, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79213, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79214 q = 1) (hb : d79999 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79214, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79214, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8399 (p : Pattern) (ha : d79217 p = 1) (hb : d80002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79207 q = 1) (hb : d79992 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79207, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79207, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79217 q = 1) (hb : d80002 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79217, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79217, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8400 (p : Pattern) (ha : d79223 p = 1) (hb : d80008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79210 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79210, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79210, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79211 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79211, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79211, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79212 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79212, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79212, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79213 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79213, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79213, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79218 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8399 q ha hb
    | true =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79219 q = 1) (hb : d80004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79219, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79219, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79220 q = 1) (hb : d80005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79220, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79220, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79221 q = 1) (hb : d80006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79221, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79221, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79222 q = 1) (hb : d80007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79222, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79222, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79223 q = 1) (hb : d80008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79223, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79223, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8401 (p : Pattern) (ha : d79228 p = 1) (hb : d80013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79227 q = 1) (hb : d80012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79227, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79227, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79228 q = 1) (hb : d80013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79228, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79228, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8402 (p : Pattern) (ha : d79235 p = 1) (hb : d80020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79233 q = 1) (hb : d80018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79233, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79233, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79234 q = 1) (hb : d80019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79234, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79234, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79235 q = 1) (hb : d80020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79235, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79235, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8403 (p : Pattern) (ha : d7728 p = 1) (hb : d79239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1142 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro155 q ha hb
  have h5 (q : Pattern) (ha : d1143 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1144 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1145 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1145, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7727 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7728 q = 1) (hb : d79239 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, d79239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7728, d79239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8404 (p : Pattern) (ha : d79244 p = 1) (hb : d80027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7729 q = 1) (hb : d79240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d79240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8403 q ha hb
    | true =>
      simp only [d7729, d79240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7730 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d79241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d79241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79241 q = 1) (hb : d80024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79242 q = 1) (hb : d80025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79242, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79242, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79243 q = 1) (hb : d80026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79243, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79243, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79244 q = 1) (hb : d80027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79244, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79244, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8405 (p : Pattern) (ha : d79257 p = 1) (hb : d80034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79229 q = 1) (hb : d80014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79229, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8401 q ha hb
    | true =>
      simp only [d79229, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79230 q = 1) (hb : d80015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79230, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79230, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79231 q = 1) (hb : d80016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79231, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79231, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79232 q = 1) (hb : d80017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79232, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79232, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79236 q = 1) (hb : d80021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79236, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8402 q ha hb
    | true =>
      simp only [d79236, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79237 q = 1) (hb : d80022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79237, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79237, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79238 q = 1) (hb : d80023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79238, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79238, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79250 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79251 q = 1) (hb : d80028 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79251, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8404 q ha hb
    | true =>
      simp only [d79251, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79209 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79252 q = 1) (hb : d80029 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79252, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79252, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79253 q = 1) (hb : d80030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79253, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79253, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79254 q = 1) (hb : d80031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79254, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79254, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79255 q = 1) (hb : d80032 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79255, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79255, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79256 q = 1) (hb : d80033 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79256, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79256, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79257 q = 1) (hb : d80034 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79257, d80034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79257, d80034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8406 (p : Pattern) (ha : d79258 p = 1) (hb : d80035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79227 q = 1) (hb : d80012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79227, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79227, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79258 q = 1) (hb : d80035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79258, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79258, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8407 (p : Pattern) (ha : d79263 p = 1) (hb : d80040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d79204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8396 q ha hb
    | true =>
      simp only [d1153, d79204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d79205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79233 q = 1) (hb : d80018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79233, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79233, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79234 q = 1) (hb : d80019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79234, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79234, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79263 q = 1) (hb : d80040 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79263, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79263, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8408 (p : Pattern) (ha : d79267 p = 1) (hb : d80044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7729 q = 1) (hb : d79240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d79240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8403 q ha hb
    | true =>
      simp only [d7729, d79240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7730 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d79241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7730, d79241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79241 q = 1) (hb : d80024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79242 q = 1) (hb : d80025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79242, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79242, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79243 q = 1) (hb : d80026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79243, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79243, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79267 q = 1) (hb : d80044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79267, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79267, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8409 (p : Pattern) (ha : d79275 p = 1) (hb : d80051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79229 q = 1) (hb : d80014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79229, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8401 q ha hb
    | true =>
      simp only [d79229, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79230 q = 1) (hb : d80015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79230, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79230, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79231 q = 1) (hb : d80016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79231, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79231, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79232 q = 1) (hb : d80017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79232, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79232, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79236 q = 1) (hb : d80021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79236, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8402 q ha hb
    | true =>
      simp only [d79236, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79237 q = 1) (hb : d80022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79237, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79237, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79238 q = 1) (hb : d80023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79238, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79238, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79250 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79251 q = 1) (hb : d80028 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79251, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8404 q ha hb
    | true =>
      simp only [d79251, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79209 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79252 q = 1) (hb : d80029 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79252, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79252, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79209 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8397 q ha hb
    | true =>
      simp only [d79209, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79253 q = 1) (hb : d80030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79253, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79253, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79254 q = 1) (hb : d80031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79254, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79254, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79255 q = 1) (hb : d80032 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79255, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79255, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79256 q = 1) (hb : d80033 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79256, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79256, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79259 q = 1) (hb : d80036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79259, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8406 q ha hb
    | true =>
      simp only [d79259, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79260 q = 1) (hb : d80037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79260, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79260, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79261 q = 1) (hb : d80038 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79261, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79261, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79262 q = 1) (hb : d80039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79262, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79262, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79264 q = 1) (hb : d80041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79264, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8407 q ha hb
    | true =>
      simp only [d79264, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d79265 q = 1) (hb : d80042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79265, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79265, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d79266 q = 1) (hb : d80043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79266, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d79266, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d79268 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d79269 q = 1) (hb : d80045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79269, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8408 q ha hb
    | true =>
      simp only [d79269, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d79218 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79270 q = 1) (hb : d80046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79270, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d79270, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d79218 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8399 q ha hb
    | true =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d79271 q = 1) (hb : d80047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79271, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d79271, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d79272 q = 1) (hb : d80048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79272, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79272, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d79273 q = 1) (hb : d80049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79273, d80049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d79273, d80049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d79274 q = 1) (hb : d80050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79274, d80050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79274, d80050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d79275 q = 1) (hb : d80051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79275, d80051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79275, d80051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8410 (p : Pattern) (ha : d79289 p = 1) (hb : d80058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79268 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79269 q = 1) (hb : d80045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79269, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8408 q ha hb
    | true =>
      simp only [d79269, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79218 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79270 q = 1) (hb : d80046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79270, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79270, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79218 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8399 q ha hb
    | true =>
      simp only [d79218, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79271 q = 1) (hb : d80047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79271, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79271, d80047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79272 q = 1) (hb : d80048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79272, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79272, d80048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79287 q = 1) (hb : d80056 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79287, d80056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79287, d80056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79288 q = 1) (hb : d80057 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79288, d80057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79288, d80057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79289 q = 1) (hb : d80058 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79289, d80058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79289, d80058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8411 (p : Pattern) (ha : d7834 p = 1) (hb : d79295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1415 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7833 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7834 q = 1) (hb : d79295 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, d79295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7834, d79295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8412 (p : Pattern) (ha : d79300 p = 1) (hb : d80067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79297 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7835 q = 1) (hb : d79296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d79296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8411 q ha hb
    | true =>
      simp only [d7835, d79296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7836 q = 1) (hb : d79297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d79297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7836, d79297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79297 q = 1) (hb : d80064 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79298 q = 1) (hb : d80065 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79298, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79298, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79299 q = 1) (hb : d80066 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79299, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79299, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79300 q = 1) (hb : d80067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79300, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79300, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8413 (p : Pattern) (ha : d1430 p = 1) (hb : d79308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1420 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1429 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1430 q = 1) (hb : d79308 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d79308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1430, d79308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8414 (p : Pattern) (ha : d79313 p = 1) (hb : d80073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79310 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1431 q = 1) (hb : d79309 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d79309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8413 q ha hb
    | true =>
      simp only [d1431, d79309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d79310 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d79310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1432, d79310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79310 q = 1) (hb : d80070 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79311 q = 1) (hb : d80071 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79311, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79311, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79312 q = 1) (hb : d80072 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79312, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79312, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79313 q = 1) (hb : d80073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79313, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79313, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8415 (p : Pattern) (ha : d79320 p = 1) (hb : d80079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79307 q = 1) (hb : d80068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79307, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8412 q ha hb
    | true =>
      simp only [d79307, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79315 q = 1) (hb : d80069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79315, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79315, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79314 q = 1) (hb : d80074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79314, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8414 q ha hb
    | true =>
      simp only [d79314, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79316 q = 1) (hb : d80075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79316, d80075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79316, d80075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79317 q = 1) (hb : d80076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79317, d80076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79317, d80076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79318 q = 1) (hb : d80077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79318, d80077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79318, d80077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79319 q = 1) (hb : d80078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79319, d80078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79319, d80078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79320 q = 1) (hb : d80079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79320, d80079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79320, d80079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8416 (p : Pattern) (ha : d79326 p = 1) (hb : d80085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79215 q = 1) (hb : d80000 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79215, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79215, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8398 q ha hb
  have h2 (q : Pattern) (ha : d79216 q = 1) (hb : d80001 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79216, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79216, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79224 q = 1) (hb : d80009 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79224, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8398 q ha hb
    | true =>
      simp only [d79224, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8400 q ha hb
  have h4 (q : Pattern) (ha : d79225 q = 1) (hb : d80010 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79225, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79225, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79226 q = 1) (hb : d80011 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79226, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79226, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79276 q = 1) (hb : d80052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79276, d80052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8405 q ha hb
    | true =>
      simp only [d79276, d80052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8409 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d79283 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d79284 q = 1) (hb : d80053 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79284, d80053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79284, d80053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d79285 q = 1) (hb : d80054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79285, d80054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79285, d80054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d79286 q = 1) (hb : d80055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79286, d80055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79286, d80055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79290 q = 1) (hb : d80059 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79290, d80059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79290, d80059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8410 q ha hb
  have h12 (q : Pattern) (ha : d79291 q = 1) (hb : d80060 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79291, d80060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79291, d80060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79292 q = 1) (hb : d80061 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79292, d80061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79292, d80061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79293 q = 1) (hb : d80062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79293, d80062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79293, d80062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d79294 q = 1) (hb : d80063 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79294, d80063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79294, d80063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79321 q = 1) (hb : d80080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79321, d80080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79321, d80080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8415 q ha hb
  have h17 (q : Pattern) (ha : d79322 q = 1) (hb : d80081 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79322, d80081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79322, d80081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79323 q = 1) (hb : d80082 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79323, d80082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d79323, d80082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d79324 q = 1) (hb : d80083 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79324, d80083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79324, d80083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79325 q = 1) (hb : d80084 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79325, d80084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d79325, d80084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d79326 q = 1) (hb : d80085 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79326, d80085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79326, d80085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8417 (p : Pattern) (ha : d79332 p = 1) (hb : d80091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79327 q = 1) (hb : d80086 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79327, d80086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79327, d80086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8416 q ha hb
  have h2 (q : Pattern) (ha : d79328 q = 1) (hb : d80087 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79328, d80087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79328, d80087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79329 q = 1) (hb : d80088 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79329, d80088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79329, d80088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79330 q = 1) (hb : d80089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79330, d80089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79330, d80089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79331 q = 1) (hb : d80090 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79331, d80090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79331, d80090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79332 q = 1) (hb : d80091 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79332, d80091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79332, d80091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8418 (p : Pattern) (ha : d1613 p = 1) (hb : d79336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1603 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro213 q ha hb
  have h2 (q : Pattern) (ha : d1604 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1605 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1607 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1612 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1613 q = 1) (hb : d79336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d79336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1613, d79336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8419 (p : Pattern) (ha : d79341 p = 1) (hb : d80098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79340 q = 1) (hb : d80097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79340, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79340, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79341 q = 1) (hb : d80098 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79341, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79341, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8420 (p : Pattern) (ha : d79347 p = 1) (hb : d80104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79343 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79343, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79343, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79344 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79344, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79344, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79345 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79345, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79345, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79346 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79346, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79346, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79347 q = 1) (hb : d80104 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79347, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79347, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8421 (p : Pattern) (ha : d79350 p = 1) (hb : d80107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79340 q = 1) (hb : d80097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79340, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79340, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79350 q = 1) (hb : d80107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79350, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79350, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8422 (p : Pattern) (ha : d79356 p = 1) (hb : d80113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79343 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79343, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79343, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79344 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79344, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79344, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79345 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79345, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79345, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79346 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79346, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79346, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79351 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8421 q ha hb
    | true =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79352 q = 1) (hb : d80109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79352, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79352, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79353 q = 1) (hb : d80110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79353, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79353, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79354 q = 1) (hb : d80111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79354, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79354, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79355 q = 1) (hb : d80112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79355, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79355, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79356 q = 1) (hb : d80113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79356, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79356, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8423 (p : Pattern) (ha : d79361 p = 1) (hb : d80118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79360 q = 1) (hb : d80117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79360, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79360, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79361 q = 1) (hb : d80118 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79361, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79361, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8424 (p : Pattern) (ha : d79368 p = 1) (hb : d80125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79366 q = 1) (hb : d80123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79366, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79366, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79367 q = 1) (hb : d80124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79367, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79367, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79368 q = 1) (hb : d80125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79368, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79368, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8425 (p : Pattern) (ha : d7882 p = 1) (hb : d79372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1603 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro213 q ha hb
  have h5 (q : Pattern) (ha : d1604 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1605 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1606 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1606, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7881 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7882 q = 1) (hb : d79372 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, d79372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7882, d79372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8426 (p : Pattern) (ha : d79377 p = 1) (hb : d80132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7883 q = 1) (hb : d79373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d79373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8425 q ha hb
    | true =>
      simp only [d7883, d79373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7884 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d79374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d79374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79374 q = 1) (hb : d80129 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79375 q = 1) (hb : d80130 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79375, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79375, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79376 q = 1) (hb : d80131 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79376, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79376, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79377 q = 1) (hb : d80132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79377, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79377, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8427 (p : Pattern) (ha : d79390 p = 1) (hb : d80139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79362 q = 1) (hb : d80119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79362, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8423 q ha hb
    | true =>
      simp only [d79362, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79363 q = 1) (hb : d80120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79363, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79363, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79364 q = 1) (hb : d80121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79364, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79364, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79365 q = 1) (hb : d80122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79365, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79365, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79369 q = 1) (hb : d80126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79369, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8424 q ha hb
    | true =>
      simp only [d79369, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79370 q = 1) (hb : d80127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79370, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79370, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79371 q = 1) (hb : d80128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79371, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79371, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79384 q = 1) (hb : d80133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79384, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8426 q ha hb
    | true =>
      simp only [d79384, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79342 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79385 q = 1) (hb : d80134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79385, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79385, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79386 q = 1) (hb : d80135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79386, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79386, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79387 q = 1) (hb : d80136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79387, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79387, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79388 q = 1) (hb : d80137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79388, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79388, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79389 q = 1) (hb : d80138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79389, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79389, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79390 q = 1) (hb : d80139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79390, d80139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79390, d80139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8428 (p : Pattern) (ha : d79391 p = 1) (hb : d80140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79360 q = 1) (hb : d80117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79360, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79360, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79391 q = 1) (hb : d80140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79391, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79391, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8429 (p : Pattern) (ha : d79396 p = 1) (hb : d80145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d79337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8418 q ha hb
    | true =>
      simp only [d1614, d79337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d79338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79366 q = 1) (hb : d80123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79366, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79366, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79367 q = 1) (hb : d80124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79367, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79367, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79396 q = 1) (hb : d80145 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79396, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79396, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8430 (p : Pattern) (ha : d79400 p = 1) (hb : d80149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7883 q = 1) (hb : d79373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d79373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8425 q ha hb
    | true =>
      simp only [d7883, d79373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7884 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d79374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7884, d79374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79374 q = 1) (hb : d80129 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79375 q = 1) (hb : d80130 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79375, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79375, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79376 q = 1) (hb : d80131 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79376, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79376, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79400 q = 1) (hb : d80149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79400, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79400, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8431 (p : Pattern) (ha : d79408 p = 1) (hb : d80156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79362 q = 1) (hb : d80119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79362, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8423 q ha hb
    | true =>
      simp only [d79362, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79363 q = 1) (hb : d80120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79363, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79363, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79364 q = 1) (hb : d80121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79364, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79364, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79365 q = 1) (hb : d80122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79365, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79365, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79369 q = 1) (hb : d80126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79369, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8424 q ha hb
    | true =>
      simp only [d79369, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79370 q = 1) (hb : d80127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79370, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79370, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79371 q = 1) (hb : d80128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79371, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79371, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79384 q = 1) (hb : d80133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79384, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8426 q ha hb
    | true =>
      simp only [d79384, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79342 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79385 q = 1) (hb : d80134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79385, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79385, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79342 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8419 q ha hb
    | true =>
      simp only [d79342, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79386 q = 1) (hb : d80135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79386, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79386, d80135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79387 q = 1) (hb : d80136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79387, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79387, d80136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79388 q = 1) (hb : d80137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79388, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79388, d80137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79389 q = 1) (hb : d80138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79389, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79389, d80138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79392 q = 1) (hb : d80141 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79392, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8428 q ha hb
    | true =>
      simp only [d79392, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79393 q = 1) (hb : d80142 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79393, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79393, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79394 q = 1) (hb : d80143 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79394, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79394, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79395 q = 1) (hb : d80144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79395, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79395, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79397 q = 1) (hb : d80146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79397, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8429 q ha hb
    | true =>
      simp only [d79397, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d79398 q = 1) (hb : d80147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79398, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79398, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d79399 q = 1) (hb : d80148 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79399, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d79399, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d79401 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d79402 q = 1) (hb : d80150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79402, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8430 q ha hb
    | true =>
      simp only [d79402, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d79351 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79403 q = 1) (hb : d80151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79403, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d79403, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d79351 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8421 q ha hb
    | true =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d79404 q = 1) (hb : d80152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79404, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d79404, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d79405 q = 1) (hb : d80153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79405, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79405, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d79406 q = 1) (hb : d80154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79406, d80154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d79406, d80154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d79407 q = 1) (hb : d80155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79407, d80155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79407, d80155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d79408 q = 1) (hb : d80156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79408, d80156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79408, d80156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8432 (p : Pattern) (ha : d79422 p = 1) (hb : d80163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79402 q = 1) (hb : d80150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79402, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8430 q ha hb
    | true =>
      simp only [d79402, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79403 q = 1) (hb : d80151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79403, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79403, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79351 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8421 q ha hb
    | true =>
      simp only [d79351, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79404 q = 1) (hb : d80152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79404, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79404, d80152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79405 q = 1) (hb : d80153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79405, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79405, d80153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79420 q = 1) (hb : d80161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79420, d80161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79420, d80161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79421 q = 1) (hb : d80162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79421, d80162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79421, d80162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79422 q = 1) (hb : d80163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79422, d80163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79422, d80163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8433 (p : Pattern) (ha : d7988 p = 1) (hb : d79428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1892 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d7987 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7988 q = 1) (hb : d79428 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, d79428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7988, d79428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8434 (p : Pattern) (ha : d79433 p = 1) (hb : d80172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79430 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7989 q = 1) (hb : d79429 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d79429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8433 q ha hb
    | true =>
      simp only [d7989, d79429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7990 q = 1) (hb : d79430 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d79430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7990, d79430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79430 q = 1) (hb : d80169 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79431 q = 1) (hb : d80170 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79431, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79431, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79432 q = 1) (hb : d80171 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79432, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79432, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79433 q = 1) (hb : d80172 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79433, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79433, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8435 (p : Pattern) (ha : d1907 p = 1) (hb : d79441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro226 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1897 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1906 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1907 q = 1) (hb : d79441 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d79441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1907, d79441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8436 (p : Pattern) (ha : d79446 p = 1) (hb : d80178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79443 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1908 q = 1) (hb : d79442 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d79442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8435 q ha hb
    | true =>
      simp only [d1908, d79442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d79443 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d79443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1909, d79443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79443 q = 1) (hb : d80175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79444 q = 1) (hb : d80176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79444, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79444, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79445 q = 1) (hb : d80177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79445, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79445, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79446 q = 1) (hb : d80178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79446, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79446, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8437 (p : Pattern) (ha : d79453 p = 1) (hb : d80184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79440 q = 1) (hb : d80173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79440, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8434 q ha hb
    | true =>
      simp only [d79440, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79447 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79448 q = 1) (hb : d80174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79448, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79448, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79447 q = 1) (hb : d80179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79447, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8436 q ha hb
    | true =>
      simp only [d79447, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79449 q = 1) (hb : d80180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79449, d80180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79449, d80180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79450 q = 1) (hb : d80181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79450, d80181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79450, d80181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79451 q = 1) (hb : d80182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79451, d80182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79451, d80182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79452 q = 1) (hb : d80183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79452, d80183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79452, d80183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79453 q = 1) (hb : d80184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79453, d80184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79453, d80184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8438 (p : Pattern) (ha : d79459 p = 1) (hb : d80190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79348 q = 1) (hb : d80105 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79348, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79348, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8420 q ha hb
  have h2 (q : Pattern) (ha : d79349 q = 1) (hb : d80106 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79349, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79349, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79357 q = 1) (hb : d80114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79357, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8420 q ha hb
    | true =>
      simp only [d79357, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8422 q ha hb
  have h4 (q : Pattern) (ha : d79358 q = 1) (hb : d80115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79358, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79358, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79359 q = 1) (hb : d80116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79359, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79359, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79409 q = 1) (hb : d80157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79409, d80157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8427 q ha hb
    | true =>
      simp only [d79409, d80157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8431 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d79416 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d79417 q = 1) (hb : d80158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79417, d80158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79417, d80158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d79418 q = 1) (hb : d80159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79418, d80159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79418, d80159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d79419 q = 1) (hb : d80160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79419, d80160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79419, d80160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79423 q = 1) (hb : d80164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79423, d80164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79423, d80164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8432 q ha hb
  have h12 (q : Pattern) (ha : d79424 q = 1) (hb : d80165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79424, d80165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79424, d80165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79425 q = 1) (hb : d80166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79425, d80166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79425, d80166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79426 q = 1) (hb : d80167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79426, d80167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79426, d80167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d79427 q = 1) (hb : d80168 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79427, d80168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79427, d80168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79454 q = 1) (hb : d80185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79454, d80185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79454, d80185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8437 q ha hb
  have h17 (q : Pattern) (ha : d79455 q = 1) (hb : d80186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79455, d80186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79455, d80186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79456 q = 1) (hb : d80187 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79456, d80187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d79456, d80187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d79457 q = 1) (hb : d80188 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79457, d80188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79457, d80188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79458 q = 1) (hb : d80189 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79458, d80189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d79458, d80189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d79459 q = 1) (hb : d80190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79459, d80190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79459, d80190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8439 (p : Pattern) (ha : d79465 p = 1) (hb : d80196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79460 q = 1) (hb : d80191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79460, d80191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79460, d80191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8438 q ha hb
  have h2 (q : Pattern) (ha : d79461 q = 1) (hb : d80192 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79461, d80192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79461, d80192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79462 q = 1) (hb : d80193 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79462, d80193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79462, d80193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79463 q = 1) (hb : d80194 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79463, d80194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79463, d80194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79464 q = 1) (hb : d80195 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79464, d80195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79464, d80195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79465 q = 1) (hb : d80196 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79465, d80196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79465, d80196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8440 (p : Pattern) (ha : d2096 p = 1) (hb : d79470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2086 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro272 q ha hb
  have h2 (q : Pattern) (ha : d2087 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2088 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2090 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2090, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2095 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2096 q = 1) (hb : d79470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d79470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2096, d79470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8441 (p : Pattern) (ha : d79475 p = 1) (hb : d80204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79474 q = 1) (hb : d80203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79474, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79474, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79475 q = 1) (hb : d80204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79475, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79475, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8442 (p : Pattern) (ha : d79481 p = 1) (hb : d80210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79477 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79477, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79477, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79478 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79478, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79478, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79479 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79479, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79479, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79480 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79480, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79480, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79481 q = 1) (hb : d80210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79481, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79481, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8443 (p : Pattern) (ha : d79484 p = 1) (hb : d80213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79474 q = 1) (hb : d80203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79474, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79474, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79484 q = 1) (hb : d80213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79484, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79484, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8444 (p : Pattern) (ha : d79490 p = 1) (hb : d80219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79477 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79477, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79477, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79478 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79478, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79478, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79479 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79479, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79479, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79480 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79480, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79480, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79485 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8443 q ha hb
    | true =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79486 q = 1) (hb : d80215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79486, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79486, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79487 q = 1) (hb : d80216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79487, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79487, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79488 q = 1) (hb : d80217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79488, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79488, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79489 q = 1) (hb : d80218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79489, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79489, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79490 q = 1) (hb : d80219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79490, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79490, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8445 (p : Pattern) (ha : d79495 p = 1) (hb : d80224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79494 q = 1) (hb : d80223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79494, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79494, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79495 q = 1) (hb : d80224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79495, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79495, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8446 (p : Pattern) (ha : d79502 p = 1) (hb : d80231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79500 q = 1) (hb : d80229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79500, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79500, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79501 q = 1) (hb : d80230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79501, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79501, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79502 q = 1) (hb : d80231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79502, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79502, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8447 (p : Pattern) (ha : d8037 p = 1) (hb : d79506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2086 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro272 q ha hb
  have h5 (q : Pattern) (ha : d2087 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2088 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2089 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2089, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d8036 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8037 q = 1) (hb : d79506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, d79506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8037, d79506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8448 (p : Pattern) (ha : d79511 p = 1) (hb : d80238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8038 q = 1) (hb : d79507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d79507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8447 q ha hb
    | true =>
      simp only [d8038, d79507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8039 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d79508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d79508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79508 q = 1) (hb : d80235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79509 q = 1) (hb : d80236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79509, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79509, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79510 q = 1) (hb : d80237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79510, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79510, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79511 q = 1) (hb : d80238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79511, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79511, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8449 (p : Pattern) (ha : d79524 p = 1) (hb : d80245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79496 q = 1) (hb : d80225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79496, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8445 q ha hb
    | true =>
      simp only [d79496, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79497 q = 1) (hb : d80226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79497, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79497, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79498 q = 1) (hb : d80227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79498, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79498, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79499 q = 1) (hb : d80228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79499, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79499, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79503 q = 1) (hb : d80232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79503, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8446 q ha hb
    | true =>
      simp only [d79503, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79504 q = 1) (hb : d80233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79504, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79504, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79505 q = 1) (hb : d80234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79505, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79505, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79517 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79518 q = 1) (hb : d80239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79518, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8448 q ha hb
    | true =>
      simp only [d79518, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79476 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79519 q = 1) (hb : d80240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79519, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79519, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79520 q = 1) (hb : d80241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79520, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79520, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79521 q = 1) (hb : d80242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79521, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79521, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79522 q = 1) (hb : d80243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79522, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79522, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79523 q = 1) (hb : d80244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79523, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79523, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79524 q = 1) (hb : d80245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79524, d80245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79524, d80245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8450 (p : Pattern) (ha : d79525 p = 1) (hb : d80246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79494 q = 1) (hb : d80223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79494, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79494, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79525 q = 1) (hb : d80246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79525, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79525, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8451 (p : Pattern) (ha : d79530 p = 1) (hb : d80251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d79471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8440 q ha hb
    | true =>
      simp only [d2097, d79471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d79472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79500 q = 1) (hb : d80229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79500, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79500, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79501 q = 1) (hb : d80230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79501, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79501, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79530 q = 1) (hb : d80251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79530, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79530, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro8452 (p : Pattern) (ha : d79534 p = 1) (hb : d80255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8038 q = 1) (hb : d79507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d79507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8447 q ha hb
    | true =>
      simp only [d8038, d79507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8039 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d79508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8039, d79508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79508 q = 1) (hb : d80235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79509 q = 1) (hb : d80236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79509, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79509, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79510 q = 1) (hb : d80237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79510, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79510, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79534 q = 1) (hb : d80255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79534, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79534, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8453 (p : Pattern) (ha : d79542 p = 1) (hb : d80262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79496 q = 1) (hb : d80225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79496, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8445 q ha hb
    | true =>
      simp only [d79496, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79497 q = 1) (hb : d80226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79497, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79497, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79498 q = 1) (hb : d80227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79498, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79498, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79499 q = 1) (hb : d80228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79499, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79499, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79503 q = 1) (hb : d80232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79503, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8446 q ha hb
    | true =>
      simp only [d79503, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79504 q = 1) (hb : d80233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79504, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79504, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79505 q = 1) (hb : d80234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79505, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79505, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d79517 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d79518 q = 1) (hb : d80239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79518, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8448 q ha hb
    | true =>
      simp only [d79518, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79476 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79519 q = 1) (hb : d80240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79519, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79519, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79476 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8441 q ha hb
    | true =>
      simp only [d79476, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79520 q = 1) (hb : d80241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79520, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79520, d80241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79521 q = 1) (hb : d80242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79521, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79521, d80242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79522 q = 1) (hb : d80243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79522, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79522, d80243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79523 q = 1) (hb : d80244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79523, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79523, d80244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79526 q = 1) (hb : d80247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79526, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8450 q ha hb
    | true =>
      simp only [d79526, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79527 q = 1) (hb : d80248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79527, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79527, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79528 q = 1) (hb : d80249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79528, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79528, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79529 q = 1) (hb : d80250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79529, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79529, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79531 q = 1) (hb : d80252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79531, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8451 q ha hb
    | true =>
      simp only [d79531, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d79532 q = 1) (hb : d80253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79532, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79532, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d79533 q = 1) (hb : d80254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79533, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d79533, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d79535 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d79536 q = 1) (hb : d80256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79536, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8452 q ha hb
    | true =>
      simp only [d79536, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d79485 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79537 q = 1) (hb : d80257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79537, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d79537, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d79485 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8443 q ha hb
    | true =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h29 (q : Pattern) (ha : d79538 q = 1) (hb : d80258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79538, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d79538, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h30 (q : Pattern) (ha : d79539 q = 1) (hb : d80259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79539, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79539, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d79540 q = 1) (hb : d80260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79540, d80260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d79540, d80260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d79541 q = 1) (hb : d80261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79541, d80261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79541, d80261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d79542 q = 1) (hb : d80262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79542, d80262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79542, d80262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro8454 (p : Pattern) (ha : d79556 p = 1) (hb : d80269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79535 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79536 q = 1) (hb : d80256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79536, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8452 q ha hb
    | true =>
      simp only [d79536, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79485 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79537 q = 1) (hb : d80257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79537, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79537, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79485 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8443 q ha hb
    | true =>
      simp only [d79485, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79538 q = 1) (hb : d80258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79538, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79538, d80258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79539 q = 1) (hb : d80259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79539, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79539, d80259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79554 q = 1) (hb : d80267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79554, d80267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79554, d80267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79555 q = 1) (hb : d80268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79555, d80268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79555, d80268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79556 q = 1) (hb : d80269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79556, d80269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79556, d80269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8455 (p : Pattern) (ha : d8143 p = 1) (hb : d79562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h5 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2370 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d8142 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8143 q = 1) (hb : d79562 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, d79562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8143, d79562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro8456 (p : Pattern) (ha : d79567 p = 1) (hb : d80278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79564 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8144 q = 1) (hb : d79563 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d79563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8455 q ha hb
    | true =>
      simp only [d8144, d79563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8145 q = 1) (hb : d79564 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d79564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8145, d79564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79564 q = 1) (hb : d80275 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79565 q = 1) (hb : d80276 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79565, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79565, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79566 q = 1) (hb : d80277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79566, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79566, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79567 q = 1) (hb : d80278 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79567, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79567, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8457 (p : Pattern) (ha : d2385 p = 1) (hb : d79575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2367 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro285 q ha hb
  have h2 (q : Pattern) (ha : d2368 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2369 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2375 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2375, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2384 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2385 q = 1) (hb : d79575 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d79575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2385, d79575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8458 (p : Pattern) (ha : d79580 p = 1) (hb : d80284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2386 q = 1) (hb : d79576 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d79576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8457 q ha hb
    | true =>
      simp only [d2386, d79576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d79577 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d79577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2387, d79577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79577 q = 1) (hb : d80281 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79578 q = 1) (hb : d80282 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79578, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79578, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d79579 q = 1) (hb : d80283 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79579, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79579, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d79580 q = 1) (hb : d80284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79580, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79580, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro8459 (p : Pattern) (ha : d79587 p = 1) (hb : d80290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79574 q = 1) (hb : d80279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79574, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8456 q ha hb
    | true =>
      simp only [d79574, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79582 q = 1) (hb : d80280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79582, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79582, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79581 q = 1) (hb : d80285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79581, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8458 q ha hb
    | true =>
      simp only [d79581, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79583 q = 1) (hb : d80286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79583, d80286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79583, d80286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79584 q = 1) (hb : d80287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79584, d80287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79584, d80287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79585 q = 1) (hb : d80288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79585, d80288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79585, d80288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79586 q = 1) (hb : d80289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79586, d80289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79586, d80289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79587 q = 1) (hb : d80290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79587, d80290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79587, d80290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8460 (p : Pattern) (ha : d79593 p = 1) (hb : d80296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79482 q = 1) (hb : d80211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79482, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79482, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8442 q ha hb
  have h2 (q : Pattern) (ha : d79483 q = 1) (hb : d80212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79483, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79483, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79491 q = 1) (hb : d80220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79491, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8442 q ha hb
    | true =>
      simp only [d79491, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8444 q ha hb
  have h4 (q : Pattern) (ha : d79492 q = 1) (hb : d80221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79492, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79492, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79493 q = 1) (hb : d80222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79493, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79493, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79543 q = 1) (hb : d80263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79543, d80263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8449 q ha hb
    | true =>
      simp only [d79543, d80263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8453 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d79550 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d79551 q = 1) (hb : d80264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79551, d80264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79551, d80264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d79552 q = 1) (hb : d80265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79552, d80265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d79552, d80265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d79553 q = 1) (hb : d80266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79553, d80266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79553, d80266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79557 q = 1) (hb : d80270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79557, d80270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79557, d80270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8454 q ha hb
  have h12 (q : Pattern) (ha : d79558 q = 1) (hb : d80271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79558, d80271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79558, d80271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d79559 q = 1) (hb : d80272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79559, d80272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79559, d80272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d79560 q = 1) (hb : d80273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79560, d80273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d79560, d80273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d79561 q = 1) (hb : d80274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79561, d80274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79561, d80274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79588 q = 1) (hb : d80291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79588, d80291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79588, d80291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8459 q ha hb
  have h17 (q : Pattern) (ha : d79589 q = 1) (hb : d80292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79589, d80292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79589, d80292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79590 q = 1) (hb : d80293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79590, d80293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d79590, d80293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d79591 q = 1) (hb : d80294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d79591, d80294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d79591, d80294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79592 q = 1) (hb : d80295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d79592, d80295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d79592, d80295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d79593 q = 1) (hb : d80296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d79593, d80296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79593, d80296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8461 (p : Pattern) (ha : d79599 p = 1) (hb : d80302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79594 q = 1) (hb : d80297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d79594, d80297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79594, d80297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8460 q ha hb
  have h2 (q : Pattern) (ha : d79595 q = 1) (hb : d80298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d79595, d80298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79595, d80298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79596 q = 1) (hb : d80299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d79596, d80299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79596, d80299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79597 q = 1) (hb : d80300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d79597, d80300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79597, d80300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79598 q = 1) (hb : d80301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d79598, d80301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79598, d80301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79599 q = 1) (hb : d80302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d79599, d80302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79599, d80302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8462 (p : Pattern) (ha : d79605 p = 1) (hb : d80308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d79070 q = 1) (hb : d79885 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79070, d79885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8351 q ha hb
    | true =>
      simp only [d79070, d79885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8373 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79201 q = 1) (hb : d79988 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79201, d79988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79201, d79988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8395 q ha hb
  have h3 (q : Pattern) (ha : d79202 q = 1) (hb : d79989 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79202, d79989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79202, d79989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d79333 q = 1) (hb : d80092 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79333, d80092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79333, d80092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8417 q ha hb
  have h5 (q : Pattern) (ha : d79334 q = 1) (hb : d80093 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79334, d80093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79334, d80093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79335 q = 1) (hb : d80094 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79335, d80094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79335, d80094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79466 q = 1) (hb : d80197 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79466, d80197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79466, d80197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8439 q ha hb
  have h8 (q : Pattern) (ha : d79467 q = 1) (hb : d80198 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79467, d80198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79467, d80198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79468 q = 1) (hb : d80199 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79468, d80199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79468, d80199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79469 q = 1) (hb : d80200 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d79469, d80200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79469, d80200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79600 q = 1) (hb : d80303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d79600, d80303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79600, d80303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8461 q ha hb
  have h12 (q : Pattern) (ha : d79601 q = 1) (hb : d80304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d79601, d80304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79601, d80304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d79602 q = 1) (hb : d80305 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d79602, d80305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79602, d80305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d79603 q = 1) (hb : d80306 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d79603, d80306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79603, d80306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79604 q = 1) (hb : d80307 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d79604, d80307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79604, d80307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79605 q = 1) (hb : d80308 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d79605, d80308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79605, d80308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro8463 (p : Pattern) (ha : d79611 p = 1) (hb : d80314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79606 q = 1) (hb : d80309 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d79606, d80309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8462 q ha hb
    | true =>
      simp only [d79606, d80309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79607 q = 1) (hb : d80310 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d79607, d80310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79607, d80310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79608 q = 1) (hb : d80311 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d79608, d80311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79608, d80311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79609 q = 1) (hb : d80312 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d79609, d80312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79609, d80312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79610 q = 1) (hb : d80313 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d79610, d80313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79610, d80313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79611 q = 1) (hb : d80314 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d79611, d80314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79611, d80314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8464 (p : Pattern) (ha : d79617 p = 1) (hb : d80320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79612 q = 1) (hb : d80315 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d79612, d80315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8463 q ha hb
    | true =>
      simp only [d79612, d80315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79613 q = 1) (hb : d80316 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d79613, d80316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79613, d80316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79614 q = 1) (hb : d80317 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d79614, d80317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79614, d80317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79615 q = 1) (hb : d80318 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d79615, d80318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79615, d80318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79616 q = 1) (hb : d80319 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d79616, d80319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79616, d80319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79617 q = 1) (hb : d80320 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d79617, d80320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79617, d80320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8465 (p : Pattern) (ha : d79623 p = 1) (hb : d80326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79618 q = 1) (hb : d80321 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d79618, d80321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8464 q ha hb
    | true =>
      simp only [d79618, d80321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79619 q = 1) (hb : d80322 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d79619, d80322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79619, d80322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79620 q = 1) (hb : d80323 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d79620, d80323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79620, d80323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79621 q = 1) (hb : d80324 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d79621, d80324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79621, d80324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79622 q = 1) (hb : d80325 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d79622, d80325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79622, d80325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79623 q = 1) (hb : d80326 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d79623, d80326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79623, d80326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8466 (p : Pattern) (ha : d79629 p = 1) (hb : d80332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79624 q = 1) (hb : d80327 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d79624, d80327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8465 q ha hb
    | true =>
      simp only [d79624, d80327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79625 q = 1) (hb : d80328 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d79625, d80328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79625, d80328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79626 q = 1) (hb : d80329 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d79626, d80329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79626, d80329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79627 q = 1) (hb : d80330 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d79627, d80330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79627, d80330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79628 q = 1) (hb : d80331 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d79628, d80331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79628, d80331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79629 q = 1) (hb : d80332 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d79629, d80332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79629, d80332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8467 (p : Pattern) (ha : d79635 p = 1) (hb : d80338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79630 q = 1) (hb : d80333 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d79630, d80333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8466 q ha hb
    | true =>
      simp only [d79630, d80333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79631 q = 1) (hb : d80334 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d79631, d80334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79631, d80334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79632 q = 1) (hb : d80335 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d79632, d80335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79632, d80335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79633 q = 1) (hb : d80336 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d79633, d80336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79633, d80336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79634 q = 1) (hb : d80337 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d79634, d80337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79634, d80337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79635 q = 1) (hb : d80338 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d79635, d80338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79635, d80338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8468 (p : Pattern) (ha : d79641 p = 1) (hb : d80344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79636 q = 1) (hb : d80339 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d79636, d80339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8467 q ha hb
    | true =>
      simp only [d79636, d80339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79637 q = 1) (hb : d80340 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d79637, d80340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79637, d80340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79638 q = 1) (hb : d80341 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d79638, d80341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79638, d80341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79639 q = 1) (hb : d80342 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d79639, d80342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79639, d80342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79640 q = 1) (hb : d80343 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d79640, d80343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79640, d80343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79641 q = 1) (hb : d80344 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d79641, d80344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79641, d80344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8469 (p : Pattern) (ha : d79647 p = 1) (hb : d80350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79642 q = 1) (hb : d80345 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d79642, d80345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8468 q ha hb
    | true =>
      simp only [d79642, d80345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79643 q = 1) (hb : d80346 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d79643, d80346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79643, d80346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79644 q = 1) (hb : d80347 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d79644, d80347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79644, d80347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79645 q = 1) (hb : d80348 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d79645, d80348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79645, d80348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79646 q = 1) (hb : d80349 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d79646, d80349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79646, d80349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79647 q = 1) (hb : d80350 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d79647, d80350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79647, d80350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8470 (p : Pattern) (ha : d53647 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8141 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8142 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8156 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8157 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8471 (p : Pattern) (ha : d69762 p = 1) (hb : d77845 p = 1) : d80353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4696 q = 1) (hb : d77845 q = 1) : d79703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4696, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4697 q = 1) (hb : d77845 q = 1) : d79704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4697, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4698 q = 1) (hb : d77845 q = 1) : d79705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4699 q = 1) (hb : d77845 q = 1) : d79706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69762 q = 1) (hb : d77845 q = 1) : d80353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69762, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69762, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8472 (p : Pattern) (ha : d69772 p = 1) (hb : d77845 p = 1) : d80363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d77845 q = 1) : d79679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8153 q ha hb
    | true =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69768 q = 1) (hb : d77845 q = 1) : d80359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69768, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69768, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69769 q = 1) (hb : d77845 q = 1) : d80360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69769, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69769, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69770 q = 1) (hb : d77845 q = 1) : d80361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69770, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69770, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69771 q = 1) (hb : d77845 q = 1) : d80362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69771, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69771, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69772 q = 1) (hb : d77845 q = 1) : d80363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69772, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69772, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8473 (p : Pattern) (ha : d69778 p = 1) (hb : d77845 p = 1) : d80369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4701 q = 1) (hb : d77845 q = 1) : d79708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8158 q ha hb
    | true =>
      simp only [d4701, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8159 q ha hb
  have h2 (q : Pattern) (ha : d4702 q = 1) (hb : d77845 q = 1) : d79709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4702, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69760 q = 1) (hb : d77845 q = 1) : d80351 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69760, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69760, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69761 q = 1) (hb : d77845 q = 1) : d80352 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69761, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69761, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69763 q = 1) (hb : d77845 q = 1) : d80354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69763, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69763, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8471 q ha hb
  have h6 (q : Pattern) (ha : d69764 q = 1) (hb : d77845 q = 1) : d80355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69764, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69764, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69765 q = 1) (hb : d77845 q = 1) : d80356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69765, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69765, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69766 q = 1) (hb : d77845 q = 1) : d80357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69766, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69766, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69767 q = 1) (hb : d77845 q = 1) : d80358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69767, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69767, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69773 q = 1) (hb : d77845 q = 1) : d80364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69773, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69773, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8472 q ha hb
  have h11 (q : Pattern) (ha : d69774 q = 1) (hb : d77845 q = 1) : d80365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69774, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69774, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69775 q = 1) (hb : d77845 q = 1) : d80366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69775, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69775, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69776 q = 1) (hb : d77845 q = 1) : d80367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69776, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69776, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69777 q = 1) (hb : d77845 q = 1) : d80368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69777, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69777, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69778 q = 1) (hb : d77845 q = 1) : d80369 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69778, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69778, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8474 (p : Pattern) (ha : d69784 p = 1) (hb : d77845 p = 1) : d80375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8470 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69779 q = 1) (hb : d77845 q = 1) : d80370 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69779, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69779, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8473 q ha hb
  have h7 (q : Pattern) (ha : d69780 q = 1) (hb : d77845 q = 1) : d80371 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69780, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69780, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69781 q = 1) (hb : d77845 q = 1) : d80372 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69781, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69781, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69782 q = 1) (hb : d77845 q = 1) : d80373 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69782, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69782, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69783 q = 1) (hb : d77845 q = 1) : d80374 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69783, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69783, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69784 q = 1) (hb : d77845 q = 1) : d80375 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69784, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69784, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8475 (p : Pattern) (ha : d69787 p = 1) (hb : d77845 p = 1) : d80378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d626 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8185 q ha hb
    | true =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4781 q = 1) (hb : d77845 q = 1) : d79797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4781, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4782 q = 1) (hb : d77845 q = 1) : d79798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4782, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4783 q = 1) (hb : d77845 q = 1) : d79799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4784 q = 1) (hb : d77845 q = 1) : d79800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69787 q = 1) (hb : d77845 q = 1) : d80378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69787, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69787, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8476 (p : Pattern) (ha : d69797 p = 1) (hb : d77845 p = 1) : d80388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d720 q = 1) (hb : d77845 q = 1) : d79867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d77845, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8201 q ha hb
    | true =>
      simp only [d720, d77845, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69793 q = 1) (hb : d77845 q = 1) : d80384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69793, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69793, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69794 q = 1) (hb : d77845 q = 1) : d80385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69794, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69794, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69795 q = 1) (hb : d77845 q = 1) : d80386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69795, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69795, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69796 q = 1) (hb : d77845 q = 1) : d80387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69796, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69796, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69797 q = 1) (hb : d77845 q = 1) : d80388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69797, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69797, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8477 (p : Pattern) (ha : d69803 p = 1) (hb : d77845 p = 1) : d80394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4786 q = 1) (hb : d77845 q = 1) : d79802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8184 q ha hb
    | true =>
      simp only [d4786, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8186 q ha hb
  have h2 (q : Pattern) (ha : d4787 q = 1) (hb : d77845 q = 1) : d79803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4787, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69785 q = 1) (hb : d77845 q = 1) : d80376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69785, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69785, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69786 q = 1) (hb : d77845 q = 1) : d80377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69786, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69786, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69788 q = 1) (hb : d77845 q = 1) : d80379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69788, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69788, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8475 q ha hb
  have h6 (q : Pattern) (ha : d69789 q = 1) (hb : d77845 q = 1) : d80380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69789, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69789, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69790 q = 1) (hb : d77845 q = 1) : d80381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69790, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69790, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69791 q = 1) (hb : d77845 q = 1) : d80382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69791, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69791, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69792 q = 1) (hb : d77845 q = 1) : d80383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69792, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69792, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69798 q = 1) (hb : d77845 q = 1) : d80389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69798, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69798, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8476 q ha hb
  have h11 (q : Pattern) (ha : d69799 q = 1) (hb : d77845 q = 1) : d80390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69799, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69799, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69800 q = 1) (hb : d77845 q = 1) : d80391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69800, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69800, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69801 q = 1) (hb : d77845 q = 1) : d80392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69801, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69801, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69802 q = 1) (hb : d77845 q = 1) : d80393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69802, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69802, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69803 q = 1) (hb : d77845 q = 1) : d80394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69803, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69803, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8478 (p : Pattern) (ha : d69809 p = 1) (hb : d77845 p = 1) : d80400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69804 q = 1) (hb : d77845 q = 1) : d80395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69804, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69804, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8477 q ha hb
  have h2 (q : Pattern) (ha : d69805 q = 1) (hb : d77845 q = 1) : d80396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69805, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69805, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69806 q = 1) (hb : d77845 q = 1) : d80397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69806, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69806, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69807 q = 1) (hb : d77845 q = 1) : d80398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69807, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69807, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69808 q = 1) (hb : d77845 q = 1) : d80399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69808, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69808, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69809 q = 1) (hb : d77845 q = 1) : d80400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69809, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69809, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8479 (p : Pattern) (ha : d69813 p = 1) (hb : d77845 p = 1) : d80404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d932 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8213 q ha hb
    | true =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4876 q = 1) (hb : d77845 q = 1) : d79900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4876, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4877 q = 1) (hb : d77845 q = 1) : d79901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4877, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4878 q = 1) (hb : d77845 q = 1) : d79902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4879 q = 1) (hb : d77845 q = 1) : d79903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69813 q = 1) (hb : d77845 q = 1) : d80404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69813, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69813, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8480 (p : Pattern) (ha : d69823 p = 1) (hb : d77845 p = 1) : d80414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1053 q = 1) (hb : d77845 q = 1) : d79970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d77845, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8229 q ha hb
    | true =>
      simp only [d1053, d77845, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69819 q = 1) (hb : d77845 q = 1) : d80410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69819, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69819, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69820 q = 1) (hb : d77845 q = 1) : d80411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69820, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69820, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69821 q = 1) (hb : d77845 q = 1) : d80412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69821, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69821, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69822 q = 1) (hb : d77845 q = 1) : d80413 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69822, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69822, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69823 q = 1) (hb : d77845 q = 1) : d80414 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69823, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69823, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8481 (p : Pattern) (ha : d69829 p = 1) (hb : d77845 p = 1) : d80420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4881 q = 1) (hb : d77845 q = 1) : d79905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8212 q ha hb
    | true =>
      simp only [d4881, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8214 q ha hb
  have h2 (q : Pattern) (ha : d4882 q = 1) (hb : d77845 q = 1) : d79906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4882, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69811 q = 1) (hb : d77845 q = 1) : d80402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69811, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69811, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69812 q = 1) (hb : d77845 q = 1) : d80403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69812, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69812, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69814 q = 1) (hb : d77845 q = 1) : d80405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69814, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69814, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8479 q ha hb
  have h6 (q : Pattern) (ha : d69815 q = 1) (hb : d77845 q = 1) : d80406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69815, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69815, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69816 q = 1) (hb : d77845 q = 1) : d80407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69816, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69816, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69817 q = 1) (hb : d77845 q = 1) : d80408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69817, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69817, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69818 q = 1) (hb : d77845 q = 1) : d80409 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69818, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69818, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69824 q = 1) (hb : d77845 q = 1) : d80415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69824, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69824, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8480 q ha hb
  have h11 (q : Pattern) (ha : d69825 q = 1) (hb : d77845 q = 1) : d80416 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69825, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69825, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69826 q = 1) (hb : d77845 q = 1) : d80417 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69826, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69826, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69827 q = 1) (hb : d77845 q = 1) : d80418 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69827, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69827, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69828 q = 1) (hb : d77845 q = 1) : d80419 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69828, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69828, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69829 q = 1) (hb : d77845 q = 1) : d80420 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69829, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69829, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8482 (p : Pattern) (ha : d69835 p = 1) (hb : d77845 p = 1) : d80426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69830 q = 1) (hb : d77845 q = 1) : d80421 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69830, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69830, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8481 q ha hb
  have h2 (q : Pattern) (ha : d69831 q = 1) (hb : d77845 q = 1) : d80422 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69831, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69831, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69832 q = 1) (hb : d77845 q = 1) : d80423 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69832, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69832, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69833 q = 1) (hb : d77845 q = 1) : d80424 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69833, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69833, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69834 q = 1) (hb : d77845 q = 1) : d80425 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69834, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69834, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69835 q = 1) (hb : d77845 q = 1) : d80426 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69835, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69835, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8483 (p : Pattern) (ha : d69840 p = 1) (hb : d77845 p = 1) : d80431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1343 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8241 q ha hb
    | true =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4972 q = 1) (hb : d77845 q = 1) : d80004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4972, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4973 q = 1) (hb : d77845 q = 1) : d80005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4973, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4974 q = 1) (hb : d77845 q = 1) : d80006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4975 q = 1) (hb : d77845 q = 1) : d80007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69840 q = 1) (hb : d77845 q = 1) : d80431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69840, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69840, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8484 (p : Pattern) (ha : d69850 p = 1) (hb : d77845 p = 1) : d80441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1487 q = 1) (hb : d77845 q = 1) : d80074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d77845, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8257 q ha hb
    | true =>
      simp only [d1487, d77845, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69846 q = 1) (hb : d77845 q = 1) : d80437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69846, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69846, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69847 q = 1) (hb : d77845 q = 1) : d80438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69847, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69847, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69848 q = 1) (hb : d77845 q = 1) : d80439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69848, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69848, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69849 q = 1) (hb : d77845 q = 1) : d80440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69849, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69849, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69850 q = 1) (hb : d77845 q = 1) : d80441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69850, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69850, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8485 (p : Pattern) (ha : d69856 p = 1) (hb : d77845 p = 1) : d80447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4977 q = 1) (hb : d77845 q = 1) : d80009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8240 q ha hb
    | true =>
      simp only [d4977, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8242 q ha hb
  have h2 (q : Pattern) (ha : d4978 q = 1) (hb : d77845 q = 1) : d80010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4978, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69838 q = 1) (hb : d77845 q = 1) : d80429 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69838, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69838, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69839 q = 1) (hb : d77845 q = 1) : d80430 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69839, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69839, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69841 q = 1) (hb : d77845 q = 1) : d80432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69841, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69841, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8483 q ha hb
  have h6 (q : Pattern) (ha : d69842 q = 1) (hb : d77845 q = 1) : d80433 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69842, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69842, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69843 q = 1) (hb : d77845 q = 1) : d80434 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69843, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69843, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69844 q = 1) (hb : d77845 q = 1) : d80435 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69844, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69844, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69845 q = 1) (hb : d77845 q = 1) : d80436 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69845, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69845, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69851 q = 1) (hb : d77845 q = 1) : d80442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69851, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69851, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8484 q ha hb
  have h11 (q : Pattern) (ha : d69852 q = 1) (hb : d77845 q = 1) : d80443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69852, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69852, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69853 q = 1) (hb : d77845 q = 1) : d80444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69853, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69853, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69854 q = 1) (hb : d77845 q = 1) : d80445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69854, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69854, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69855 q = 1) (hb : d77845 q = 1) : d80446 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69855, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69855, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69856 q = 1) (hb : d77845 q = 1) : d80447 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69856, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69856, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8486 (p : Pattern) (ha : d69862 p = 1) (hb : d77845 p = 1) : d80453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69857 q = 1) (hb : d77845 q = 1) : d80448 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69857, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69857, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8485 q ha hb
  have h2 (q : Pattern) (ha : d69858 q = 1) (hb : d77845 q = 1) : d80449 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69858, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69858, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69859 q = 1) (hb : d77845 q = 1) : d80450 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69859, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69859, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69860 q = 1) (hb : d77845 q = 1) : d80451 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69860, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69860, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69861 q = 1) (hb : d77845 q = 1) : d80452 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69861, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69861, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69862 q = 1) (hb : d77845 q = 1) : d80453 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69862, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69862, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8487 (p : Pattern) (ha : d69868 p = 1) (hb : d77845 p = 1) : d80459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1820 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8269 q ha hb
    | true =>
      simp only [d1820, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5083 q = 1) (hb : d77845 q = 1) : d80109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5083, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5084 q = 1) (hb : d77845 q = 1) : d80110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5084, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5085 q = 1) (hb : d77845 q = 1) : d80111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5086 q = 1) (hb : d77845 q = 1) : d80112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69868 q = 1) (hb : d77845 q = 1) : d80459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69868, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69868, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8488 (p : Pattern) (ha : d69878 p = 1) (hb : d77845 p = 1) : d80469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1964 q = 1) (hb : d77845 q = 1) : d80179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d77845, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8285 q ha hb
    | true =>
      simp only [d1964, d77845, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69874 q = 1) (hb : d77845 q = 1) : d80465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69874, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69874, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69875 q = 1) (hb : d77845 q = 1) : d80466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69875, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69875, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69876 q = 1) (hb : d77845 q = 1) : d80467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69876, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69876, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69877 q = 1) (hb : d77845 q = 1) : d80468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69877, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69877, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69878 q = 1) (hb : d77845 q = 1) : d80469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69878, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69878, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8489 (p : Pattern) (ha : d69884 p = 1) (hb : d77845 p = 1) : d80475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5088 q = 1) (hb : d77845 q = 1) : d80114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8268 q ha hb
    | true =>
      simp only [d5088, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8270 q ha hb
  have h2 (q : Pattern) (ha : d5089 q = 1) (hb : d77845 q = 1) : d80115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5089, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69866 q = 1) (hb : d77845 q = 1) : d80457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69866, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69866, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69867 q = 1) (hb : d77845 q = 1) : d80458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69867, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69867, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69869 q = 1) (hb : d77845 q = 1) : d80460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69869, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69869, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8487 q ha hb
  have h6 (q : Pattern) (ha : d69870 q = 1) (hb : d77845 q = 1) : d80461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69870, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69870, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69871 q = 1) (hb : d77845 q = 1) : d80462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69871, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69871, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69872 q = 1) (hb : d77845 q = 1) : d80463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69872, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69872, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69873 q = 1) (hb : d77845 q = 1) : d80464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69873, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69873, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69879 q = 1) (hb : d77845 q = 1) : d80470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69879, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69879, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8488 q ha hb
  have h11 (q : Pattern) (ha : d69880 q = 1) (hb : d77845 q = 1) : d80471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69880, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69880, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69881 q = 1) (hb : d77845 q = 1) : d80472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69881, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69881, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69882 q = 1) (hb : d77845 q = 1) : d80473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69882, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69882, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69883 q = 1) (hb : d77845 q = 1) : d80474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69883, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69883, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69884 q = 1) (hb : d77845 q = 1) : d80475 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69884, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69884, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8490 (p : Pattern) (ha : d69890 p = 1) (hb : d77845 p = 1) : d80481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69885 q = 1) (hb : d77845 q = 1) : d80476 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69885, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69885, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8489 q ha hb
  have h2 (q : Pattern) (ha : d69886 q = 1) (hb : d77845 q = 1) : d80477 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69886, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69886, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69887 q = 1) (hb : d77845 q = 1) : d80478 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69887, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69887, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69888 q = 1) (hb : d77845 q = 1) : d80479 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69888, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69888, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69889 q = 1) (hb : d77845 q = 1) : d80480 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69889, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69889, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69890 q = 1) (hb : d77845 q = 1) : d80481 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69890, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69890, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8491 (p : Pattern) (ha : d69897 p = 1) (hb : d77845 p = 1) : d80488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2298 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8297 q ha hb
    | true =>
      simp only [d2298, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5200 q = 1) (hb : d77845 q = 1) : d80215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5200, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5201 q = 1) (hb : d77845 q = 1) : d80216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5201, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5202 q = 1) (hb : d77845 q = 1) : d80217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5203 q = 1) (hb : d77845 q = 1) : d80218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69897 q = 1) (hb : d77845 q = 1) : d80488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69897, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69897, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8492 (p : Pattern) (ha : d69907 p = 1) (hb : d77845 p = 1) : d80498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2442 q = 1) (hb : d77845 q = 1) : d80285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d77845, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8313 q ha hb
    | true =>
      simp only [d2442, d77845, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69903 q = 1) (hb : d77845 q = 1) : d80494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69903, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69903, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69904 q = 1) (hb : d77845 q = 1) : d80495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69904, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69904, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69905 q = 1) (hb : d77845 q = 1) : d80496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69905, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69905, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69906 q = 1) (hb : d77845 q = 1) : d80497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69906, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69906, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69907 q = 1) (hb : d77845 q = 1) : d80498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69907, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69907, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8493 (p : Pattern) (ha : d69913 p = 1) (hb : d77845 p = 1) : d80504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5205 q = 1) (hb : d77845 q = 1) : d80220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8296 q ha hb
    | true =>
      simp only [d5205, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8298 q ha hb
  have h2 (q : Pattern) (ha : d5206 q = 1) (hb : d77845 q = 1) : d80221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5206, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69895 q = 1) (hb : d77845 q = 1) : d80486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69895, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69895, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69896 q = 1) (hb : d77845 q = 1) : d80487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69896, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69896, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69898 q = 1) (hb : d77845 q = 1) : d80489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69898, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69898, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8491 q ha hb
  have h6 (q : Pattern) (ha : d69899 q = 1) (hb : d77845 q = 1) : d80490 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69899, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69899, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69900 q = 1) (hb : d77845 q = 1) : d80491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69900, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69900, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69901 q = 1) (hb : d77845 q = 1) : d80492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69901, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69901, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69902 q = 1) (hb : d77845 q = 1) : d80493 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69902, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69902, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69908 q = 1) (hb : d77845 q = 1) : d80499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69908, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69908, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8492 q ha hb
  have h11 (q : Pattern) (ha : d69909 q = 1) (hb : d77845 q = 1) : d80500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69909, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69909, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69910 q = 1) (hb : d77845 q = 1) : d80501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69910, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69910, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69911 q = 1) (hb : d77845 q = 1) : d80502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69911, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69911, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69912 q = 1) (hb : d77845 q = 1) : d80503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69912, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69912, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69913 q = 1) (hb : d77845 q = 1) : d80504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69913, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69913, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8494 (p : Pattern) (ha : d69919 p = 1) (hb : d77845 p = 1) : d80510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69914 q = 1) (hb : d77845 q = 1) : d80505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69914, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69914, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8493 q ha hb
  have h2 (q : Pattern) (ha : d69915 q = 1) (hb : d77845 q = 1) : d80506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69915, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69915, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69916 q = 1) (hb : d77845 q = 1) : d80507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69916, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69916, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69917 q = 1) (hb : d77845 q = 1) : d80508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69917, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69917, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69918 q = 1) (hb : d77845 q = 1) : d80509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69918, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69918, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69919 q = 1) (hb : d77845 q = 1) : d80510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69919, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69919, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8495 (p : Pattern) (ha : d69925 p = 1) (hb : d77845 p = 1) : d80516 p = 1 := by
  have h0 (q : Pattern) (ha : d69810 q = 1) (hb : d77845 q = 1) : d80401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69810, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8474 q ha hb
    | true =>
      simp only [d69810, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8478 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69836 q = 1) (hb : d77845 q = 1) : d80427 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69836, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69836, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8482 q ha hb
  have h3 (q : Pattern) (ha : d69837 q = 1) (hb : d77845 q = 1) : d80428 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69837, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69837, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69863 q = 1) (hb : d77845 q = 1) : d80454 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69863, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69863, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8486 q ha hb
  have h5 (q : Pattern) (ha : d69864 q = 1) (hb : d77845 q = 1) : d80455 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69864, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69864, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69865 q = 1) (hb : d77845 q = 1) : d80456 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69865, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69865, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69891 q = 1) (hb : d77845 q = 1) : d80482 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69891, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69891, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8490 q ha hb
  have h8 (q : Pattern) (ha : d69892 q = 1) (hb : d77845 q = 1) : d80483 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69892, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69892, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69893 q = 1) (hb : d77845 q = 1) : d80484 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69893, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69893, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69894 q = 1) (hb : d77845 q = 1) : d80485 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69894, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69894, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69920 q = 1) (hb : d77845 q = 1) : d80511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69920, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69920, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8494 q ha hb
  have h12 (q : Pattern) (ha : d69921 q = 1) (hb : d77845 q = 1) : d80512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69921, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69921, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69922 q = 1) (hb : d77845 q = 1) : d80513 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69922, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69922, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69923 q = 1) (hb : d77845 q = 1) : d80514 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69923, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69923, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69924 q = 1) (hb : d77845 q = 1) : d80515 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69924, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69924, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69925 q = 1) (hb : d77845 q = 1) : d80516 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69925, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69925, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8496 (p : Pattern) (ha : d69931 p = 1) (hb : d77845 p = 1) : d80522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69926 q = 1) (hb : d77845 q = 1) : d80517 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69926, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8495 q ha hb
    | true =>
      simp only [d69926, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69927 q = 1) (hb : d77845 q = 1) : d80518 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69927, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69927, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69928 q = 1) (hb : d77845 q = 1) : d80519 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69928, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69928, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69929 q = 1) (hb : d77845 q = 1) : d80520 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69929, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69929, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69930 q = 1) (hb : d77845 q = 1) : d80521 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69930, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69930, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69931 q = 1) (hb : d77845 q = 1) : d80522 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69931, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69931, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8497 (p : Pattern) (ha : d69937 p = 1) (hb : d77845 p = 1) : d80528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69932 q = 1) (hb : d77845 q = 1) : d80523 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69932, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8496 q ha hb
    | true =>
      simp only [d69932, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69933 q = 1) (hb : d77845 q = 1) : d80524 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69933, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69933, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69934 q = 1) (hb : d77845 q = 1) : d80525 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69934, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69934, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69935 q = 1) (hb : d77845 q = 1) : d80526 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69935, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69935, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69936 q = 1) (hb : d77845 q = 1) : d80527 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69936, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69936, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69937 q = 1) (hb : d77845 q = 1) : d80528 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69937, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69937, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8498 (p : Pattern) (ha : d69943 p = 1) (hb : d77845 p = 1) : d80534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69938 q = 1) (hb : d77845 q = 1) : d80529 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69938, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8497 q ha hb
    | true =>
      simp only [d69938, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69939 q = 1) (hb : d77845 q = 1) : d80530 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69939, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69939, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69940 q = 1) (hb : d77845 q = 1) : d80531 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69940, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69940, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69941 q = 1) (hb : d77845 q = 1) : d80532 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69941, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69941, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69942 q = 1) (hb : d77845 q = 1) : d80533 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69942, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69942, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69943 q = 1) (hb : d77845 q = 1) : d80534 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69943, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69943, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8499 (p : Pattern) (ha : d69949 p = 1) (hb : d77845 p = 1) : d80540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69944 q = 1) (hb : d77845 q = 1) : d80535 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69944, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8498 q ha hb
    | true =>
      simp only [d69944, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69945 q = 1) (hb : d77845 q = 1) : d80536 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69945, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69945, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69946 q = 1) (hb : d77845 q = 1) : d80537 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69946, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69946, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69947 q = 1) (hb : d77845 q = 1) : d80538 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69947, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69947, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69948 q = 1) (hb : d77845 q = 1) : d80539 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69948, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69948, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69949 q = 1) (hb : d77845 q = 1) : d80540 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69949, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69949, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
