import NetHack.Soko22Hazard87.AndIntroBlocks0018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro4750 (p : Pattern) (ha : d71626 p = 1) (hb : d72263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70396 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71614 q = 1) (hb : d72254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71614, d72254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71614, d72254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70409 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71615 q = 1) (hb : d72255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71615, d72255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71615, d72255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71616 q = 1) (hb : d72256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71616, d72256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71616, d72256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71617 q = 1) (hb : d72257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71617, d72257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71617, d72257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70417 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70420 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70421 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71622 q = 1) (hb : d72259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71622, d72259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71622, d72259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70424 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71623 q = 1) (hb : d72260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71623, d72260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71623, d72260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71624 q = 1) (hb : d72261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71624, d72261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71624, d72261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71625 q = 1) (hb : d72262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71625, d72262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71625, d72262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71626 q = 1) (hb : d72263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71626, d72263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71626, d72263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4751 (p : Pattern) (ha : d72016 p = 1) (hb : d72270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71622 q = 1) (hb : d72259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71622, d72259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71622, d72259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70424 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71623 q = 1) (hb : d72260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71623, d72260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71623, d72260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71624 q = 1) (hb : d72268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71624, d72268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71624, d72268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71625 q = 1) (hb : d72269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71625, d72269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71625, d72269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72016 q = 1) (hb : d72270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72016, d72270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72016, d72270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4752 (p : Pattern) (ha : d72027 p = 1) (hb : d72280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70443 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72023 q = 1) (hb : d72276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72023, d72276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72023, d72276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70451 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d72024 q = 1) (hb : d72277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72024, d72277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72024, d72277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72025 q = 1) (hb : d72278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72025, d72278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72025, d72278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72026 q = 1) (hb : d72279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72026, d72279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72026, d72279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72027 q = 1) (hb : d72280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72027, d72280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72027, d72280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4753 (p : Pattern) (ha : d72033 p = 1) (hb : d72286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71627 q = 1) (hb : d72264 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71627, d72264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4749 q ha hb
    | true =>
      simp only [d71627, d72264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4750 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71628 q = 1) (hb : d72265 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71628, d72265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71628, d72265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72014 q = 1) (hb : d72266 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72014, d72266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72014, d72266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d72015 q = 1) (hb : d72267 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72015, d72267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72015, d72267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72017 q = 1) (hb : d72271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72017, d72271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72017, d72271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4751 q ha hb
  have h7 (q : Pattern) (ha : d72018 q = 1) (hb : d72272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72018, d72272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72018, d72272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d72019 q = 1) (hb : d72273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72019, d72273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d72019, d72273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d72020 q = 1) (hb : d72274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72020, d72274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72020, d72274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d72021 q = 1) (hb : d72275 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72021, d72275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72021, d72275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72028 q = 1) (hb : d72281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72028, d72281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72028, d72281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4752 q ha hb
  have h12 (q : Pattern) (ha : d72029 q = 1) (hb : d72282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72029, d72282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72029, d72282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d72030 q = 1) (hb : d72283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72030, d72283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72030, d72283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d72031 q = 1) (hb : d72284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72031, d72284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d72031, d72284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d72032 q = 1) (hb : d72285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72032, d72285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72032, d72285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d72033 q = 1) (hb : d72286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72033, d72286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72033, d72286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4754 (p : Pattern) (ha : d72039 p = 1) (hb : d72292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72034 q = 1) (hb : d72287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72034, d72287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72034, d72287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4753 q ha hb
  have h2 (q : Pattern) (ha : d72035 q = 1) (hb : d72288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72035, d72288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72035, d72288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72036 q = 1) (hb : d72289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72036, d72289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72036, d72289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72037 q = 1) (hb : d72290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72037, d72290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72037, d72290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72038 q = 1) (hb : d72291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72038, d72291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72038, d72291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72039 q = 1) (hb : d72292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72039, d72292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72039, d72292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4755 (p : Pattern) (ha : d71693 p = 1) (hb : d72299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71689 q = 1) (hb : d72295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71689, d72295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71689, d72295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70506 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71690 q = 1) (hb : d72296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71690, d72296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71690, d72296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71691 q = 1) (hb : d72297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71691, d72297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71691, d72297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71692 q = 1) (hb : d72298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71692, d72298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71692, d72298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71693 q = 1) (hb : d72299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71693, d72299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71693, d72299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4756 (p : Pattern) (ha : d71701 p = 1) (hb : d72304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70498 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71689 q = 1) (hb : d72295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71689, d72295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71689, d72295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70506 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71690 q = 1) (hb : d72296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71690, d72296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71690, d72296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71691 q = 1) (hb : d72297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71691, d72297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71691, d72297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71692 q = 1) (hb : d72298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71692, d72298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71692, d72298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70514 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70517 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70518 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71697 q = 1) (hb : d72300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71697, d72300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71697, d72300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70521 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71698 q = 1) (hb : d72301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71698, d72301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71698, d72301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71699 q = 1) (hb : d72302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71699, d72302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71699, d72302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71700 q = 1) (hb : d72303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71700, d72303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71700, d72303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71701 q = 1) (hb : d72304 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71701, d72304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71701, d72304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4757 (p : Pattern) (ha : d72044 p = 1) (hb : d72311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71697 q = 1) (hb : d72300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71697, d72300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71697, d72300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71698 q = 1) (hb : d72301 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71698, d72301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71698, d72301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71699 q = 1) (hb : d72309 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71699, d72309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71699, d72309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71700 q = 1) (hb : d72310 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71700, d72310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71700, d72310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72044 q = 1) (hb : d72311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72044, d72311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72044, d72311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4758 (p : Pattern) (ha : d72055 p = 1) (hb : d72321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72050 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72051 q = 1) (hb : d72317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72051, d72317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72051, d72317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70548 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d72052 q = 1) (hb : d72318 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72052, d72318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72052, d72318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72053 q = 1) (hb : d72319 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72053, d72319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72053, d72319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72054 q = 1) (hb : d72320 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72054, d72320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72054, d72320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72055 q = 1) (hb : d72321 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72055, d72321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72055, d72321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4759 (p : Pattern) (ha : d72061 p = 1) (hb : d72327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70488 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71702 q = 1) (hb : d72305 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71702, d72305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4755 q ha hb
    | true =>
      simp only [d71702, d72305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4756 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71703 q = 1) (hb : d72306 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71703, d72306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71703, d72306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72042 q = 1) (hb : d72307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72042, d72307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72042, d72307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d72043 q = 1) (hb : d72308 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72043, d72308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72043, d72308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72045 q = 1) (hb : d72312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72045, d72312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72045, d72312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4757 q ha hb
  have h7 (q : Pattern) (ha : d72046 q = 1) (hb : d72313 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72046, d72313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72046, d72313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d72047 q = 1) (hb : d72314 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72047, d72314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d72047, d72314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d72048 q = 1) (hb : d72315 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72048, d72315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72048, d72315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d72049 q = 1) (hb : d72316 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72049, d72316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72049, d72316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72056 q = 1) (hb : d72322 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72056, d72322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72056, d72322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4758 q ha hb
  have h12 (q : Pattern) (ha : d72057 q = 1) (hb : d72323 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72057, d72323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72057, d72323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d72058 q = 1) (hb : d72324 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72058, d72324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72058, d72324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d72059 q = 1) (hb : d72325 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72059, d72325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d72059, d72325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d72060 q = 1) (hb : d72326 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72060, d72326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72060, d72326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d72061 q = 1) (hb : d72327 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72061, d72327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72061, d72327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4760 (p : Pattern) (ha : d72067 p = 1) (hb : d72333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72062 q = 1) (hb : d72328 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72062, d72328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72062, d72328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4759 q ha hb
  have h2 (q : Pattern) (ha : d72063 q = 1) (hb : d72329 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72063, d72329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72063, d72329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72064 q = 1) (hb : d72330 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72064, d72330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72064, d72330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72065 q = 1) (hb : d72331 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72065, d72331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72065, d72331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72066 q = 1) (hb : d72332 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72066, d72332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72066, d72332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72067 q = 1) (hb : d72333 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72067, d72333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72067, d72333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4761 (p : Pattern) (ha : d71769 p = 1) (hb : d72341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70599 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71765 q = 1) (hb : d72337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71765, d72337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71765, d72337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70604 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71766 q = 1) (hb : d72338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71766, d72338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71766, d72338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71767 q = 1) (hb : d72339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71767, d72339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71767, d72339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71768 q = 1) (hb : d72340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71768, d72340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71768, d72340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71769 q = 1) (hb : d72341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71769, d72341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71769, d72341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4762 (p : Pattern) (ha : d71777 p = 1) (hb : d72346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70591 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71765 q = 1) (hb : d72337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71765, d72337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71765, d72337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70604 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71766 q = 1) (hb : d72338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71766, d72338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71766, d72338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71767 q = 1) (hb : d72339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71767, d72339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71767, d72339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71768 q = 1) (hb : d72340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71768, d72340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71768, d72340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70612 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70615 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70616 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71773 q = 1) (hb : d72342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71773, d72342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71773, d72342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71774 q = 1) (hb : d72343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71774, d72343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71774, d72343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71775 q = 1) (hb : d72344 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71775, d72344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71775, d72344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71776 q = 1) (hb : d72345 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71776, d72345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71776, d72345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71777 q = 1) (hb : d72346 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71777, d72346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71777, d72346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4763 (p : Pattern) (ha : d72073 p = 1) (hb : d72353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70616 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71773 q = 1) (hb : d72342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71773, d72342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71773, d72342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71774 q = 1) (hb : d72343 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71774, d72343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71774, d72343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71775 q = 1) (hb : d72351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71775, d72351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71775, d72351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71776 q = 1) (hb : d72352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71776, d72352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71776, d72352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72073 q = 1) (hb : d72353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72073, d72353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72073, d72353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4764 (p : Pattern) (ha : d72084 p = 1) (hb : d72363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70638 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72079 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72080 q = 1) (hb : d72359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72080, d72359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72080, d72359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70646 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d72081 q = 1) (hb : d72360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72081, d72360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72081, d72360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72082 q = 1) (hb : d72361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72082, d72361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72082, d72361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72083 q = 1) (hb : d72362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72083, d72362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72083, d72362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72084 q = 1) (hb : d72363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72084, d72363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72084, d72363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4765 (p : Pattern) (ha : d72090 p = 1) (hb : d72369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71778 q = 1) (hb : d72347 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71778, d72347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4761 q ha hb
    | true =>
      simp only [d71778, d72347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4762 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71779 q = 1) (hb : d72348 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71779, d72348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71779, d72348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72071 q = 1) (hb : d72349 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72071, d72349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72071, d72349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d72072 q = 1) (hb : d72350 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72072, d72350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72072, d72350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72074 q = 1) (hb : d72354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72074, d72354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72074, d72354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4763 q ha hb
  have h7 (q : Pattern) (ha : d72075 q = 1) (hb : d72355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72075, d72355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72075, d72355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d72076 q = 1) (hb : d72356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72076, d72356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d72076, d72356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d72077 q = 1) (hb : d72357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72077, d72357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72077, d72357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d72078 q = 1) (hb : d72358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72078, d72358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72078, d72358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72085 q = 1) (hb : d72364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72085, d72364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72085, d72364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4764 q ha hb
  have h12 (q : Pattern) (ha : d72086 q = 1) (hb : d72365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72086, d72365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72086, d72365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d72087 q = 1) (hb : d72366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72087, d72366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72087, d72366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d72088 q = 1) (hb : d72367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72088, d72367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d72088, d72367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d72089 q = 1) (hb : d72368 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72089, d72368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72089, d72368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d72090 q = 1) (hb : d72369 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72090, d72369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72090, d72369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4766 (p : Pattern) (ha : d72096 p = 1) (hb : d72375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72091 q = 1) (hb : d72370 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72091, d72370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72091, d72370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4765 q ha hb
  have h2 (q : Pattern) (ha : d72092 q = 1) (hb : d72371 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72092, d72371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72092, d72371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72093 q = 1) (hb : d72372 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72093, d72372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72093, d72372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72094 q = 1) (hb : d72373 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72094, d72373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72094, d72373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72095 q = 1) (hb : d72374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72095, d72374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72095, d72374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72096 q = 1) (hb : d72375 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72096, d72375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72096, d72375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4767 (p : Pattern) (ha : d71846 p = 1) (hb : d72384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70698 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71842 q = 1) (hb : d72380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71842, d72380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71842, d72380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70703 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71843 q = 1) (hb : d72381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71843, d72381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71843, d72381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71844 q = 1) (hb : d72382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71844, d72382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71844, d72382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71845 q = 1) (hb : d72383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71845, d72383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71845, d72383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71846 q = 1) (hb : d72384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71846, d72384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71846, d72384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4768 (p : Pattern) (ha : d71854 p = 1) (hb : d72389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71842 q = 1) (hb : d72380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71842, d72380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71842, d72380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d70703 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71843 q = 1) (hb : d72381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71843, d72381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71843, d72381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71844 q = 1) (hb : d72382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71844, d72382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71844, d72382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71845 q = 1) (hb : d72383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71845, d72383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71845, d72383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70711 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70714 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70715 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d71850 q = 1) (hb : d72385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71850, d72385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71850, d72385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70718 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d71851 q = 1) (hb : d72386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71851, d72386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d71851, d72386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d71852 q = 1) (hb : d72387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71852, d72387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d71852, d72387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d71853 q = 1) (hb : d72388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71853, d72388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71853, d72388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d71854 q = 1) (hb : d72389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71854, d72389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71854, d72389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4769 (p : Pattern) (ha : d72103 p = 1) (hb : d72396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71850 q = 1) (hb : d72385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71850, d72385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71850, d72385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70718 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71851 q = 1) (hb : d72386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71851, d72386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71851, d72386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71852 q = 1) (hb : d72394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71852, d72394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71852, d72394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71853 q = 1) (hb : d72395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71853, d72395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71853, d72395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72103 q = 1) (hb : d72396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72103, d72396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72103, d72396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4770 (p : Pattern) (ha : d72114 p = 1) (hb : d72406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72110 q = 1) (hb : d72402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72110, d72402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72110, d72402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70745 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d72111 q = 1) (hb : d72403 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72111, d72403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72111, d72403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72112 q = 1) (hb : d72404 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72112, d72404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72112, d72404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72113 q = 1) (hb : d72405 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72113, d72405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72113, d72405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72114 q = 1) (hb : d72406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72114, d72406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72114, d72406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4771 (p : Pattern) (ha : d72120 p = 1) (hb : d72412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70685 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71855 q = 1) (hb : d72390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71855, d72390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4767 q ha hb
    | true =>
      simp only [d71855, d72390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4768 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71856 q = 1) (hb : d72391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71856, d72391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71856, d72391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72101 q = 1) (hb : d72392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72101, d72392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72101, d72392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d72102 q = 1) (hb : d72393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72102, d72393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72102, d72393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72104 q = 1) (hb : d72397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72104, d72397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72104, d72397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4769 q ha hb
  have h7 (q : Pattern) (ha : d72105 q = 1) (hb : d72398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72105, d72398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72105, d72398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d72106 q = 1) (hb : d72399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72106, d72399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d72106, d72399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d72107 q = 1) (hb : d72400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72107, d72400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72107, d72400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d72108 q = 1) (hb : d72401 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72108, d72401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72108, d72401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72115 q = 1) (hb : d72407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72115, d72407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72115, d72407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4770 q ha hb
  have h12 (q : Pattern) (ha : d72116 q = 1) (hb : d72408 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72116, d72408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72116, d72408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d72117 q = 1) (hb : d72409 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72117, d72409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72117, d72409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d72118 q = 1) (hb : d72410 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72118, d72410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d72118, d72410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d72119 q = 1) (hb : d72411 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72119, d72411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72119, d72411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d72120 q = 1) (hb : d72412 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72120, d72412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72120, d72412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro4772 (p : Pattern) (ha : d72126 p = 1) (hb : d72418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72121 q = 1) (hb : d72413 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72121, d72413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72121, d72413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4771 q ha hb
  have h2 (q : Pattern) (ha : d72122 q = 1) (hb : d72414 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72122, d72414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72122, d72414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72123 q = 1) (hb : d72415 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72123, d72415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72123, d72415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72124 q = 1) (hb : d72416 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72124, d72416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72124, d72416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72125 q = 1) (hb : d72417 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72125, d72417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72125, d72417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72126 q = 1) (hb : d72418 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72126, d72418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72126, d72418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4773 (p : Pattern) (ha : d72132 p = 1) (hb : d72424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d72013 q = 1) (hb : d72253 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72013, d72253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4742 q ha hb
    | true =>
      simp only [d72013, d72253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4748 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72040 q = 1) (hb : d72293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72040, d72293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72040, d72293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4754 q ha hb
  have h3 (q : Pattern) (ha : d72041 q = 1) (hb : d72294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72041, d72294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72041, d72294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72068 q = 1) (hb : d72334 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72068, d72334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72068, d72334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4760 q ha hb
  have h5 (q : Pattern) (ha : d72069 q = 1) (hb : d72335 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72069, d72335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72069, d72335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72070 q = 1) (hb : d72336 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72070, d72336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72070, d72336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72097 q = 1) (hb : d72376 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72097, d72376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72097, d72376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4766 q ha hb
  have h8 (q : Pattern) (ha : d72098 q = 1) (hb : d72377 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72098, d72377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72098, d72377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72099 q = 1) (hb : d72378 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72099, d72378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72099, d72378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72100 q = 1) (hb : d72379 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72100, d72379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72100, d72379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72127 q = 1) (hb : d72419 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72127, d72419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72127, d72419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4772 q ha hb
  have h12 (q : Pattern) (ha : d72128 q = 1) (hb : d72420 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72128, d72420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72128, d72420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d72129 q = 1) (hb : d72421 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72129, d72421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72129, d72421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d72130 q = 1) (hb : d72422 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72130, d72422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72130, d72422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72131 q = 1) (hb : d72423 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d72131, d72423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72131, d72423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d72132 q = 1) (hb : d72424 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d72132, d72424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72132, d72424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4774 (p : Pattern) (ha : d72138 p = 1) (hb : d72430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72133 q = 1) (hb : d72425 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d72133, d72425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4773 q ha hb
    | true =>
      simp only [d72133, d72425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72134 q = 1) (hb : d72426 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d72134, d72426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72134, d72426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72135 q = 1) (hb : d72427 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d72135, d72427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72135, d72427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72136 q = 1) (hb : d72428 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d72136, d72428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72136, d72428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72137 q = 1) (hb : d72429 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d72137, d72429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72137, d72429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72138 q = 1) (hb : d72430 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d72138, d72430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72138, d72430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4775 (p : Pattern) (ha : d72144 p = 1) (hb : d72436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72139 q = 1) (hb : d72431 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d72139, d72431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4774 q ha hb
    | true =>
      simp only [d72139, d72431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72140 q = 1) (hb : d72432 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d72140, d72432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72140, d72432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72141 q = 1) (hb : d72433 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d72141, d72433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72141, d72433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72142 q = 1) (hb : d72434 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d72142, d72434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72142, d72434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72143 q = 1) (hb : d72435 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d72143, d72435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72143, d72435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72144 q = 1) (hb : d72436 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d72144, d72436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72144, d72436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4776 (p : Pattern) (ha : d72150 p = 1) (hb : d72442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72145 q = 1) (hb : d72437 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d72145, d72437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4775 q ha hb
    | true =>
      simp only [d72145, d72437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72146 q = 1) (hb : d72438 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d72146, d72438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72146, d72438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72147 q = 1) (hb : d72439 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d72147, d72439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72147, d72439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72148 q = 1) (hb : d72440 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d72148, d72440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72148, d72440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72149 q = 1) (hb : d72441 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d72149, d72441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72149, d72441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72150 q = 1) (hb : d72442 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d72150, d72442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72150, d72442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4777 (p : Pattern) (ha : d72156 p = 1) (hb : d72448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72151 q = 1) (hb : d72443 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d72151, d72443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4776 q ha hb
    | true =>
      simp only [d72151, d72443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72152 q = 1) (hb : d72444 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d72152, d72444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72152, d72444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72153 q = 1) (hb : d72445 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d72153, d72445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72153, d72445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72154 q = 1) (hb : d72446 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d72154, d72446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72154, d72446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72155 q = 1) (hb : d72447 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d72155, d72447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72155, d72447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72156 q = 1) (hb : d72448 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d72156, d72448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72156, d72448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4778 (p : Pattern) (ha : d72162 p = 1) (hb : d72454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72157 q = 1) (hb : d72449 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d72157, d72449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4777 q ha hb
    | true =>
      simp only [d72157, d72449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72158 q = 1) (hb : d72450 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d72158, d72450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72158, d72450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72159 q = 1) (hb : d72451 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d72159, d72451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72159, d72451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72160 q = 1) (hb : d72452 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d72160, d72452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72160, d72452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72161 q = 1) (hb : d72453 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d72161, d72453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72161, d72453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72162 q = 1) (hb : d72454 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d72162, d72454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72162, d72454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4779 (p : Pattern) (ha : d72168 p = 1) (hb : d72460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72163 q = 1) (hb : d72455 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d72163, d72455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4778 q ha hb
    | true =>
      simp only [d72163, d72455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72164 q = 1) (hb : d72456 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d72164, d72456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72164, d72456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72165 q = 1) (hb : d72457 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d72165, d72457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72165, d72457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72166 q = 1) (hb : d72458 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d72166, d72458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72166, d72458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72167 q = 1) (hb : d72459 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d72167, d72459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72167, d72459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72168 q = 1) (hb : d72460 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d72168, d72460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72168, d72460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4780 (p : Pattern) (ha : d72174 p = 1) (hb : d72466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72169 q = 1) (hb : d72461 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d72169, d72461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4779 q ha hb
    | true =>
      simp only [d72169, d72461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72170 q = 1) (hb : d72462 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d72170, d72462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72170, d72462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72171 q = 1) (hb : d72463 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d72171, d72463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72171, d72463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72172 q = 1) (hb : d72464 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d72172, d72464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72172, d72464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72173 q = 1) (hb : d72465 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d72173, d72465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72173, d72465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72174 q = 1) (hb : d72466 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d72174, d72466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72174, d72466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4781 (p : Pattern) (ha : d95 p = 1) (hb : d61358 p = 1) : d3324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57 q = 1) (hb : d61358 q = 1) : d3320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d61358, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57, d61358, d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58 q = 1) (hb : d61358 q = 1) : d3321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58, d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d59 q = 1) (hb : d61358 q = 1) : d3322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d60 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d61 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d63 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d64 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d65 q = 1) (hb : d61358 q = 1) : d3323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d65, d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d89 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d90 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d90, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d91 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d91, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d92 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d93 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d94 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d95 q = 1) (hb : d61358 q = 1) : d3324 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d95, d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4782 (p : Pattern) (ha : d58614 p = 1) (hb : d61358 p = 1) : d72471 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d106 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d106, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h8 (q : Pattern) (ha : d113 q = 1) (hb : d61358 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d61358, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113, d61358, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d114 q = 1) (hb : d61358 q = 1) : d3331 q = 1 := by
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
  have h13 (q : Pattern) (ha : d58610 q = 1) (hb : d61358 q = 1) : d72467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58610, d61358, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58610, d61358, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58611 q = 1) (hb : d61358 q = 1) : d72468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58611, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58611, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58612 q = 1) (hb : d61358 q = 1) : d72469 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58612, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58612, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h19 (q : Pattern) (ha : d4351 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4351, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4352 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4353 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58613 q = 1) (hb : d61358 q = 1) : d72470 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58613, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58613, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h25 (q : Pattern) (ha : d4361 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4361, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4362 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4363 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4364 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58614 q = 1) (hb : d61358 q = 1) : d72471 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58614, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4783 (p : Pattern) (ha : d58624 p = 1) (hb : d61358 p = 1) : d72481 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d286 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h8 (q : Pattern) (ha : d293 q = 1) (hb : d61358 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d61358, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293, d61358, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d294 q = 1) (hb : d61358 q = 1) : d3345 q = 1 := by
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
  have h13 (q : Pattern) (ha : d58620 q = 1) (hb : d61358 q = 1) : d72477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58620, d61358, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58620, d61358, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58621 q = 1) (hb : d61358 q = 1) : d72478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58621, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58621, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58622 q = 1) (hb : d61358 q = 1) : d72479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58622, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58622, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4385 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4386 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4387 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4387, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4388 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4389 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58623 q = 1) (hb : d61358 q = 1) : d72480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58623, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58623, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4395 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4396 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4397 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4397, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4398 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4399 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4400 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58624 q = 1) (hb : d61358 q = 1) : d72481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58624, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4784 (p : Pattern) (ha : d58630 p = 1) (hb : d61358 p = 1) : d72487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d61358 q = 1) : d3325 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4781 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d61358 q = 1) : d3326 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d61358 q = 1) : d3327 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d61358 q = 1) : d3328 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58615 q = 1) (hb : d61358 q = 1) : d72472 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58615, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4782 q ha hb
  have h6 (q : Pattern) (ha : d58616 q = 1) (hb : d61358 q = 1) : d72473 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58616, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58617 q = 1) (hb : d61358 q = 1) : d72474 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58617, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58618 q = 1) (hb : d61358 q = 1) : d72475 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58618, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58619 q = 1) (hb : d61358 q = 1) : d72476 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58619, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58625 q = 1) (hb : d61358 q = 1) : d72482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58625, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4783 q ha hb
  have h11 (q : Pattern) (ha : d58626 q = 1) (hb : d61358 q = 1) : d72483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58626, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58627 q = 1) (hb : d61358 q = 1) : d72484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58627, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58628 q = 1) (hb : d61358 q = 1) : d72485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58628, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58629 q = 1) (hb : d61358 q = 1) : d72486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58629, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58630 q = 1) (hb : d61358 q = 1) : d72487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58630, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4785 (p : Pattern) (ha : d58635 p = 1) (hb : d61358 p = 1) : d72492 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d499 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d499, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h8 (q : Pattern) (ha : d509 q = 1) (hb : d61358 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d61358, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d509, d61358, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d510 q = 1) (hb : d61358 q = 1) : d3361 q = 1 := by
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
  have h13 (q : Pattern) (ha : d58631 q = 1) (hb : d61358 q = 1) : d72488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58631, d61358, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58631, d61358, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58632 q = 1) (hb : d61358 q = 1) : d72489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58632, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58632, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58633 q = 1) (hb : d61358 q = 1) : d72490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58633, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58633, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4422 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4423 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4424 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4424, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4425 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4426 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58634 q = 1) (hb : d61358 q = 1) : d72491 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58634, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58634, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4432 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4433 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4434 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4434, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4435 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4436 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4437 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58635 q = 1) (hb : d61358 q = 1) : d72492 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58635, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4786 (p : Pattern) (ha : d58641 p = 1) (hb : d61358 p = 1) : d72498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d61358 q = 1) : d72493 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4785 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d61358 q = 1) : d72494 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d61358 q = 1) : d72495 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d61358 q = 1) : d72496 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d61358 q = 1) : d72497 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d61358 q = 1) : d72498 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4787 (p : Pattern) (ha : d58647 p = 1) (hb : d61358 p = 1) : d72504 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d791 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d791, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h8 (q : Pattern) (ha : d801 q = 1) (hb : d61358 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d61358, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d801, d61358, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d802 q = 1) (hb : d61358 q = 1) : d3378 q = 1 := by
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
  have h13 (q : Pattern) (ha : d58643 q = 1) (hb : d61358 q = 1) : d72500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58643, d61358, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58643, d61358, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58644 q = 1) (hb : d61358 q = 1) : d72501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58644, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58644, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58645 q = 1) (hb : d61358 q = 1) : d72502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58645, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58645, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4460 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4461 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4462 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4462, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4463 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4464 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58646 q = 1) (hb : d61358 q = 1) : d72503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58646, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58646, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4470 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4471 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4472 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4472, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4473 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4474 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4475 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58647 q = 1) (hb : d61358 q = 1) : d72504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58647, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4788 (p : Pattern) (ha : d58653 p = 1) (hb : d61358 p = 1) : d72510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d61358 q = 1) : d72505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4787 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d61358 q = 1) : d72506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d61358 q = 1) : d72507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d61358 q = 1) : d72508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d61358 q = 1) : d72509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d61358 q = 1) : d72510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4789 (p : Pattern) (ha : d58660 p = 1) (hb : d61358 p = 1) : d72517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1169 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1170 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1170, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1180 q = 1) (hb : d61358 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d61358, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1180, d61358, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1181 q = 1) (hb : d61358 q = 1) : d3396 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1181, d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51738 q = 1) : d51738 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51742 q = 1) (hb : d61357 q = 1) : d61589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51742, d61357, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d58656 q = 1) (hb : d61358 q = 1) : d72513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58656, d61358, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58656, d61358, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58657 q = 1) (hb : d61358 q = 1) : d72514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58657, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58658 q = 1) (hb : d61358 q = 1) : d72515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58658, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4499 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4500 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4501 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4501, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4502 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4503 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58659 q = 1) (hb : d61358 q = 1) : d72516 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58659, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4509 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4510 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4511 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4511, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4512 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4513 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4514 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58660 q = 1) (hb : d61358 q = 1) : d72517 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58660, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4790 (p : Pattern) (ha : d58666 p = 1) (hb : d61358 p = 1) : d72523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d61358 q = 1) : d72518 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4789 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d61358 q = 1) : d72519 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d61358 q = 1) : d72520 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d61358 q = 1) : d72521 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d61358 q = 1) : d72522 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d61358 q = 1) : d72523 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4791 (p : Pattern) (ha : d58674 p = 1) (hb : d61358 p = 1) : d72531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1630 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1631 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1631, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1641 q = 1) (hb : d61358 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d61358, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1641, d61358, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1642 q = 1) (hb : d61358 q = 1) : d3415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1642, d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51766 q = 1) : d51766 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51770 q = 1) (hb : d61357 q = 1) : d61604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51770, d61357, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d58670 q = 1) (hb : d61358 q = 1) : d72527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58670, d61358, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58670, d61358, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58671 q = 1) (hb : d61358 q = 1) : d72528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58671, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58672 q = 1) (hb : d61358 q = 1) : d72529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58672, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4539 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4540 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4541 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4541, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4542 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4543 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58673 q = 1) (hb : d61358 q = 1) : d72530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58673, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4549 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4550 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4551 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4551, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4552 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4553 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4554 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58674 q = 1) (hb : d61358 q = 1) : d72531 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58674, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4792 (p : Pattern) (ha : d58680 p = 1) (hb : d61358 p = 1) : d72537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d61358 q = 1) : d72532 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4791 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d61358 q = 1) : d72533 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d61358 q = 1) : d72534 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d61358 q = 1) : d72535 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d61358 q = 1) : d72536 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d61358 q = 1) : d72537 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4793 (p : Pattern) (ha : d58689 p = 1) (hb : d61358 p = 1) : d72546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2113 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2114 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2114, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2124 q = 1) (hb : d61358 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d61358, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2124, d61358, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2125 q = 1) (hb : d61358 q = 1) : d3435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2125, d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d51795 q = 1) : d51795 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d51799 q = 1) (hb : d61357 q = 1) : d61620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d51799, d61357, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d58685 q = 1) (hb : d61358 q = 1) : d72542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58685, d61358, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58685, d61358, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d58686 q = 1) (hb : d61358 q = 1) : d72543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58686, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d58686, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58687 q = 1) (hb : d61358 q = 1) : d72544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58687, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58687, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4580 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4581 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d4582 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4582, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d4583 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h21 (q : Pattern) (ha : d4584 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h22 (q : Pattern) (ha : d58688 q = 1) (hb : d61358 q = 1) : d72545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58688, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58688, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d4590 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4591 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d4592 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d4592, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h26 (q : Pattern) (ha : d4593 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d4593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h27 (q : Pattern) (ha : d4594 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h28 (q : Pattern) (ha : d4595 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h29 (q : Pattern) (ha : d58689 q = 1) (hb : d61358 q = 1) : d72546 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d58689, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro4794 (p : Pattern) (ha : d58695 p = 1) (hb : d61358 p = 1) : d72552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d61358 q = 1) : d72547 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4793 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d61358 q = 1) : d72548 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d61358 q = 1) : d72549 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d61358 q = 1) : d72550 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d61358 q = 1) : d72551 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d61358 q = 1) : d72552 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4795 (p : Pattern) (ha : d58701 p = 1) (hb : d61358 p = 1) : d72558 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d61358 q = 1) : d72499 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4784 q ha hb
    | true =>
      simp only [d58642, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4786 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d61358 q = 1) : d72511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4788 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d61358 q = 1) : d72512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d61358 q = 1) : d72524 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4790 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d61358 q = 1) : d72525 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d61358 q = 1) : d72526 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d61358 q = 1) : d72538 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4792 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d61358 q = 1) : d72539 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d61358 q = 1) : d72540 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d61358 q = 1) : d72541 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d61358 q = 1) : d72553 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4794 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d61358 q = 1) : d72554 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d61358 q = 1) : d72555 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d61358 q = 1) : d72556 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d61358 q = 1) : d72557 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d61358 q = 1) : d72558 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4796 (p : Pattern) (ha : d58707 p = 1) (hb : d61358 p = 1) : d72564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d61358 q = 1) : d72559 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4795 q ha hb
    | true =>
      simp only [d58702, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d61358 q = 1) : d72560 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d61358 q = 1) : d72561 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d61358 q = 1) : d72562 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d61358 q = 1) : d72563 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d61358 q = 1) : d72564 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4797 (p : Pattern) (ha : d58713 p = 1) (hb : d61358 p = 1) : d72570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d61358 q = 1) : d72565 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4796 q ha hb
    | true =>
      simp only [d58708, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d61358 q = 1) : d72566 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d61358 q = 1) : d72567 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d61358 q = 1) : d72568 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d61358 q = 1) : d72569 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d61358 q = 1) : d72570 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4798 (p : Pattern) (ha : d58719 p = 1) (hb : d61358 p = 1) : d72576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d61358 q = 1) : d72571 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4797 q ha hb
    | true =>
      simp only [d58714, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d61358 q = 1) : d72572 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d61358 q = 1) : d72573 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d61358 q = 1) : d72574 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d61358 q = 1) : d72575 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d61358 q = 1) : d72576 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4799 (p : Pattern) (ha : d58725 p = 1) (hb : d61358 p = 1) : d72582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d61358 q = 1) : d72577 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4798 q ha hb
    | true =>
      simp only [d58720, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d61358 q = 1) : d72578 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d61358 q = 1) : d72579 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d61358 q = 1) : d72580 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d61358 q = 1) : d72581 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d61358 q = 1) : d72582 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4800 (p : Pattern) (ha : d58731 p = 1) (hb : d61358 p = 1) : d72588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d61358 q = 1) : d72583 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4799 q ha hb
    | true =>
      simp only [d58726, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d61358 q = 1) : d72584 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d61358 q = 1) : d72585 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d61358 q = 1) : d72586 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d61358 q = 1) : d72587 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d61358 q = 1) : d72588 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4801 (p : Pattern) (ha : d58737 p = 1) (hb : d61358 p = 1) : d72594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d61358 q = 1) : d72589 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4800 q ha hb
    | true =>
      simp only [d58732, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d61358 q = 1) : d72590 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d61358 q = 1) : d72591 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d61358 q = 1) : d72592 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58736 q = 1) (hb : d61358 q = 1) : d72593 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58737 q = 1) (hb : d61358 q = 1) : d72594 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58737, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4802 (p : Pattern) (ha : d58743 p = 1) (hb : d61358 p = 1) : d72600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d61358 q = 1) : d72595 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4801 q ha hb
    | true =>
      simp only [d58738, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d61358 q = 1) : d72596 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d61358 q = 1) : d72597 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d61358 q = 1) : d72598 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d61358 q = 1) : d72599 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d61358 q = 1) : d72600 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4803 (p : Pattern) (ha : d61379 p = 1) (hb : d72471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3329 q = 1) (hb : d61371 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3330 q = 1) (hb : d61372 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3331 q = 1) (hb : d61373 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61374 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61374, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d61374, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61375 q = 1) (hb : d72467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61375, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61375, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61376 q = 1) (hb : d72468 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61376, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61376, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61377 q = 1) (hb : d72469 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61377, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61377, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61378 q = 1) (hb : d72470 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61378, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61378, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61379 q = 1) (hb : d72471 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61379, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61379, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4804 (p : Pattern) (ha : d61394 p = 1) (hb : d72481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3343 q = 1) (hb : d61385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3344 q = 1) (hb : d61386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3345 q = 1) (hb : d61387 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61388 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61388, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d61388, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61390 q = 1) (hb : d72477 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61390, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61390, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61391 q = 1) (hb : d72478 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61391, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61391, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61392 q = 1) (hb : d72479 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61392, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61392, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61393 q = 1) (hb : d72480 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61393, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61393, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61394 q = 1) (hb : d72481 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61394, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61394, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4805 (p : Pattern) (ha : d61400 p = 1) (hb : d72487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d61367 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1514 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d61368 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d61369 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d61370 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61380 q = 1) (hb : d72472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61380, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61380, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4803 q ha hb
  have h6 (q : Pattern) (ha : d61381 q = 1) (hb : d72473 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61381, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61381, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61382 q = 1) (hb : d72474 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61382, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61382, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61383 q = 1) (hb : d72475 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61383, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61383, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61384 q = 1) (hb : d72476 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61384, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d61384, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61395 q = 1) (hb : d72482 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61395, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61395, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4804 q ha hb
  have h11 (q : Pattern) (ha : d61396 q = 1) (hb : d72483 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61396, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61396, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61397 q = 1) (hb : d72484 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61397, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61397, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61398 q = 1) (hb : d72485 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61398, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61398, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61399 q = 1) (hb : d72486 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61399, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61399, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61400 q = 1) (hb : d72487 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61400, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61400, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4806 (p : Pattern) (ha : d61410 p = 1) (hb : d72492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3359 q = 1) (hb : d61401 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3360 q = 1) (hb : d61402 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3361 q = 1) (hb : d61403 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61404 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61404, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d61404, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61405 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61406 q = 1) (hb : d72488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61406, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61406, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61407 q = 1) (hb : d72489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61407, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61407, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61408 q = 1) (hb : d72490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61408, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61408, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61409 q = 1) (hb : d72491 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61409, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61409, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61410 q = 1) (hb : d72492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61410, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61410, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4807 (p : Pattern) (ha : d61416 p = 1) (hb : d72498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61411 q = 1) (hb : d72493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61411, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61411, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4806 q ha hb
  have h2 (q : Pattern) (ha : d61412 q = 1) (hb : d72494 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61412, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61412, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61413 q = 1) (hb : d72495 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61413, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61413, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61414 q = 1) (hb : d72496 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61414, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61414, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61415 q = 1) (hb : d72497 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61415, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61415, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61416 q = 1) (hb : d72498 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61416, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61416, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4808 (p : Pattern) (ha : d61427 p = 1) (hb : d72504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3376 q = 1) (hb : d61418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3377 q = 1) (hb : d61419 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3378 q = 1) (hb : d61420 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61421 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61421, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d61421, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61422 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61423 q = 1) (hb : d72500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61423, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61423, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61424 q = 1) (hb : d72501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61424, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61424, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61425 q = 1) (hb : d72502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61425, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61425, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61426 q = 1) (hb : d72503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61426, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61426, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61427 q = 1) (hb : d72504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61427, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61427, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4809 (p : Pattern) (ha : d61433 p = 1) (hb : d72510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61428 q = 1) (hb : d72505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61428, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61428, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4808 q ha hb
  have h2 (q : Pattern) (ha : d61429 q = 1) (hb : d72506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61429, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61429, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61430 q = 1) (hb : d72507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61430, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61430, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61431 q = 1) (hb : d72508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61431, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61431, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61432 q = 1) (hb : d72509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61432, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61432, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61433 q = 1) (hb : d72510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61433, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61433, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4810 (p : Pattern) (ha : d61445 p = 1) (hb : d72517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3394 q = 1) (hb : d61436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3395 q = 1) (hb : d61437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3396 q = 1) (hb : d61438 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61439 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61439, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d61439, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61440 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61441 q = 1) (hb : d72513 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61441, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61441, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61442 q = 1) (hb : d72514 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61442, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61442, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61443 q = 1) (hb : d72515 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61443, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61443, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61444 q = 1) (hb : d72516 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61444, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61444, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61445 q = 1) (hb : d72517 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61445, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61445, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4811 (p : Pattern) (ha : d61451 p = 1) (hb : d72523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61446 q = 1) (hb : d72518 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61446, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61446, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4810 q ha hb
  have h2 (q : Pattern) (ha : d61447 q = 1) (hb : d72519 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61447, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61447, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61448 q = 1) (hb : d72520 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61448, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61448, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61449 q = 1) (hb : d72521 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61449, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61449, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61450 q = 1) (hb : d72522 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61450, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61450, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61451 q = 1) (hb : d72523 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61451, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61451, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4812 (p : Pattern) (ha : d61464 p = 1) (hb : d72531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3413 q = 1) (hb : d61455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3414 q = 1) (hb : d61456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3415 q = 1) (hb : d61457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61458 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61458, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d61458, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61459 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61460 q = 1) (hb : d72527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61460, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61460, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61461 q = 1) (hb : d72528 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61461, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61461, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61462 q = 1) (hb : d72529 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61462, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61462, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61463 q = 1) (hb : d72530 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61463, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61463, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61464 q = 1) (hb : d72531 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61464, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61464, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4813 (p : Pattern) (ha : d61470 p = 1) (hb : d72537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61465 q = 1) (hb : d72532 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61465, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61465, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4812 q ha hb
  have h2 (q : Pattern) (ha : d61466 q = 1) (hb : d72533 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61466, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61466, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61467 q = 1) (hb : d72534 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61467, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61467, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61468 q = 1) (hb : d72535 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61468, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61468, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61469 q = 1) (hb : d72536 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61469, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61469, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61470 q = 1) (hb : d72537 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61470, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61470, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4814 (p : Pattern) (ha : d61484 p = 1) (hb : d72546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3433 q = 1) (hb : d61475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3434 q = 1) (hb : d61476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3435 q = 1) (hb : d61477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61478 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61478, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d61478, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d61479 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d61480 q = 1) (hb : d72542 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61480, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61480, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d61481 q = 1) (hb : d72543 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61481, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61481, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d61482 q = 1) (hb : d72544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61482, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d61482, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61483 q = 1) (hb : d72545 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61483, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d61483, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d61484 q = 1) (hb : d72546 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61484, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61484, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro4815 (p : Pattern) (ha : d61490 p = 1) (hb : d72552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61485 q = 1) (hb : d72547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61485, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61485, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4814 q ha hb
  have h2 (q : Pattern) (ha : d61486 q = 1) (hb : d72548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61486, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61486, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61487 q = 1) (hb : d72549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61487, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61487, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61488 q = 1) (hb : d72550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61488, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61488, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61489 q = 1) (hb : d72551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61489, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61489, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61490 q = 1) (hb : d72552 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61490, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61490, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4816 (p : Pattern) (ha : d61496 p = 1) (hb : d72558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61417 q = 1) (hb : d72499 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61417, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4805 q ha hb
    | true =>
      simp only [d61417, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4807 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61434 q = 1) (hb : d72511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61434, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61434, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4809 q ha hb
  have h3 (q : Pattern) (ha : d61435 q = 1) (hb : d72512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61435, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61435, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61452 q = 1) (hb : d72524 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61452, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61452, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4811 q ha hb
  have h5 (q : Pattern) (ha : d61453 q = 1) (hb : d72525 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61453, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61453, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61454 q = 1) (hb : d72526 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61454, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61454, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61471 q = 1) (hb : d72538 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61471, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61471, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4813 q ha hb
  have h8 (q : Pattern) (ha : d61472 q = 1) (hb : d72539 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61472, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61472, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61473 q = 1) (hb : d72540 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61473, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61473, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61474 q = 1) (hb : d72541 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61474, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61474, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61491 q = 1) (hb : d72553 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61491, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61491, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4815 q ha hb
  have h12 (q : Pattern) (ha : d61492 q = 1) (hb : d72554 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61492, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61492, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61493 q = 1) (hb : d72555 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61493, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61493, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61494 q = 1) (hb : d72556 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61494, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61494, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61495 q = 1) (hb : d72557 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61495, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61495, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61496 q = 1) (hb : d72558 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61496, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61496, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4817 (p : Pattern) (ha : d61502 p = 1) (hb : d72564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61497 q = 1) (hb : d72559 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61497, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4816 q ha hb
    | true =>
      simp only [d61497, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61498 q = 1) (hb : d72560 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61498, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61498, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61499 q = 1) (hb : d72561 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61499, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61499, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61500 q = 1) (hb : d72562 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61500, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61500, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61501 q = 1) (hb : d72563 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61501, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61501, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61502 q = 1) (hb : d72564 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61502, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61502, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4818 (p : Pattern) (ha : d61508 p = 1) (hb : d72570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61503 q = 1) (hb : d72565 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61503, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4817 q ha hb
    | true =>
      simp only [d61503, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61504 q = 1) (hb : d72566 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61504, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61504, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61505 q = 1) (hb : d72567 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61505, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61505, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61506 q = 1) (hb : d72568 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61506, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61506, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61507 q = 1) (hb : d72569 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61507, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61507, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61508 q = 1) (hb : d72570 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61508, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61508, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4819 (p : Pattern) (ha : d61514 p = 1) (hb : d72576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61509 q = 1) (hb : d72571 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61509, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4818 q ha hb
    | true =>
      simp only [d61509, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61510 q = 1) (hb : d72572 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61510, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61510, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61511 q = 1) (hb : d72573 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61511, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61511, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61512 q = 1) (hb : d72574 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61512, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61512, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61513 q = 1) (hb : d72575 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61513, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61513, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61514 q = 1) (hb : d72576 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61514, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61514, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4820 (p : Pattern) (ha : d61520 p = 1) (hb : d72582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61515 q = 1) (hb : d72577 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61515, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4819 q ha hb
    | true =>
      simp only [d61515, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61516 q = 1) (hb : d72578 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61516, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61516, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61517 q = 1) (hb : d72579 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61517, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61517, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61518 q = 1) (hb : d72580 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61518, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61518, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61519 q = 1) (hb : d72581 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61519, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61519, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61520 q = 1) (hb : d72582 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61520, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61520, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4821 (p : Pattern) (ha : d61526 p = 1) (hb : d72588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61521 q = 1) (hb : d72583 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61521, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4820 q ha hb
    | true =>
      simp only [d61521, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61522 q = 1) (hb : d72584 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61522, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61522, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61523 q = 1) (hb : d72585 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61523, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61523, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61524 q = 1) (hb : d72586 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61524, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61524, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61525 q = 1) (hb : d72587 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61525, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61525, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61526 q = 1) (hb : d72588 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61526, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61526, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4822 (p : Pattern) (ha : d61532 p = 1) (hb : d72594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61527 q = 1) (hb : d72589 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61527, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4821 q ha hb
    | true =>
      simp only [d61527, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61528 q = 1) (hb : d72590 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61528, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61528, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61529 q = 1) (hb : d72591 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61529, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61529, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61530 q = 1) (hb : d72592 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61530, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61530, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61531 q = 1) (hb : d72593 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61531, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61531, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61532 q = 1) (hb : d72594 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61532, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61532, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4823 (p : Pattern) (ha : d61538 p = 1) (hb : d72600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61533 q = 1) (hb : d72595 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61533, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4822 q ha hb
    | true =>
      simp only [d61533, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61534 q = 1) (hb : d72596 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61534, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61534, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61535 q = 1) (hb : d72597 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61535, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61535, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61536 q = 1) (hb : d72598 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61536, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61536, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61537 q = 1) (hb : d72599 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61537, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61537, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61538 q = 1) (hb : d72600 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61538, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61538, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4824 (p : Pattern) (ha : d53647 p = 1) (hb : d61358 p = 1) : d61683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d104 q = 1) : d104 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d61357 q = 1) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112, d61357, d3329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113 q = 1) (hb : d61358 q = 1) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d61358, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d61358, d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53637 q = 1) (hb : d61358 q = 1) : d61680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53637, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53638 q = 1) (hb : d61358 q = 1) : d61681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d406 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d407 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d407, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53639 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53639, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53640 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53641 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53642 q = 1) (hb : d61358 q = 1) : d61682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53642, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d462 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d463 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d463, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53643 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53643, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53644 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53645 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53646 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53647 q = 1) (hb : d61358 q = 1) : d61683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53647, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4825 (p : Pattern) (ha : d53671 p = 1) (hb : d61358 p = 1) : d61692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d284 q = 1) : d284 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d61357 q = 1) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292, d61357, d3343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293 q = 1) (hb : d61358 q = 1) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d61358, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d61358, d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53653 q = 1) (hb : d61358 q = 1) : d61689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53653, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53654 q = 1) (hb : d61358 q = 1) : d61690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53655 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53656 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53656, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53657 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53657, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53658 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53659 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53660 q = 1) (hb : d61358 q = 1) : d61691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53660, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53665 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53666 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53666, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53667 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53667, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53668 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53669 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53670 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53671 q = 1) (hb : d61358 q = 1) : d61692 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53671, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4826 (p : Pattern) (ha : d53677 p = 1) (hb : d61358 p = 1) : d61698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d61358 q = 1) : d61684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4824 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d61358 q = 1) : d61685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d61358 q = 1) : d61686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d61358 q = 1) : d61687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d61358 q = 1) : d61688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d61358 q = 1) : d61693 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4825 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d61358 q = 1) : d61694 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d61358 q = 1) : d61695 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d61358 q = 1) : d61696 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d61358 q = 1) : d61697 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d61358 q = 1) : d61698 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4827 (p : Pattern) (ha : d53697 p = 1) (hb : d61358 p = 1) : d61702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d497 q = 1) : d497 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d507 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d61357 q = 1) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d508, d61357, d3359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d509 q = 1) (hb : d61358 q = 1) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d61358, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d61358, d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53678 q = 1) (hb : d61358 q = 1) : d61699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53678, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53679 q = 1) (hb : d61358 q = 1) : d61700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53680 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53681 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53681, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53682 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53682, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53683 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53684 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53685 q = 1) (hb : d61358 q = 1) : d61701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53685, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53691 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53692 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53692, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53693 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53693, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53694 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53695 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53696 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53697 q = 1) (hb : d61358 q = 1) : d61702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53697, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4828 (p : Pattern) (ha : d53703 p = 1) (hb : d61358 p = 1) : d61708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d61358 q = 1) : d61703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4827 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d61358 q = 1) : d61704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d61358 q = 1) : d61705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d61358 q = 1) : d61706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d61358 q = 1) : d61707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d61358 q = 1) : d61708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4829 (p : Pattern) (ha : d53724 p = 1) (hb : d61358 p = 1) : d61713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d789 q = 1) : d789 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d61357 q = 1) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d800, d61357, d3376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d801 q = 1) (hb : d61358 q = 1) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d61358, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d61358, d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53705 q = 1) (hb : d61358 q = 1) : d61710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53705, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53706 q = 1) (hb : d61358 q = 1) : d61711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53707 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53708 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53708, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53709 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53709, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53710 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53711 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53712 q = 1) (hb : d61358 q = 1) : d61712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53712, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53718 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53719 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53719, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53720 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53720, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53721 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53722 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53723 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53724 q = 1) (hb : d61358 q = 1) : d61713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53724, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4830 (p : Pattern) (ha : d53730 p = 1) (hb : d61358 p = 1) : d61719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d61358 q = 1) : d61714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4829 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d61358 q = 1) : d61715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d61358 q = 1) : d61716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d61358 q = 1) : d61717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d61358 q = 1) : d61718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d61358 q = 1) : d61719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4831 (p : Pattern) (ha : d53752 p = 1) (hb : d61358 p = 1) : d61725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1168 q = 1) : d1168 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d61357 q = 1) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1179, d61357, d3394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1180 q = 1) (hb : d61358 q = 1) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d61358, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d61358, d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53733 q = 1) (hb : d61358 q = 1) : d61722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53733, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53734 q = 1) (hb : d61358 q = 1) : d61723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53735 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53736 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53736, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53737 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53737, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53738 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53739 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53740 q = 1) (hb : d61358 q = 1) : d61724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53740, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53746 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53747 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53747, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53748 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53748, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53749 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53750 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53751 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53752 q = 1) (hb : d61358 q = 1) : d61725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53752, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4832 (p : Pattern) (ha : d53758 p = 1) (hb : d61358 p = 1) : d61731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d61358 q = 1) : d61726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4831 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d61358 q = 1) : d61727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d61358 q = 1) : d61728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d61358 q = 1) : d61729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d61358 q = 1) : d61730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d61358 q = 1) : d61731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4833 (p : Pattern) (ha : d53781 p = 1) (hb : d61358 p = 1) : d61738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1629 q = 1) : d1629 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d61357 q = 1) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1640, d61357, d3413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1641 q = 1) (hb : d61358 q = 1) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d61358, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d61358, d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53762 q = 1) (hb : d61358 q = 1) : d61735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53762, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53763 q = 1) (hb : d61358 q = 1) : d61736 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53764 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53765 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53765, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53766 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53766, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53767 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53768 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53769 q = 1) (hb : d61358 q = 1) : d61737 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53769, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53775 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53776 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53776, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53777 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53777, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53778 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53779 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53780 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53781 q = 1) (hb : d61358 q = 1) : d61738 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53781, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4834 (p : Pattern) (ha : d53787 p = 1) (hb : d61358 p = 1) : d61744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d61358 q = 1) : d61739 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4833 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d61358 q = 1) : d61740 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d61358 q = 1) : d61741 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d61358 q = 1) : d61742 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d61358 q = 1) : d61743 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d61358 q = 1) : d61744 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4835 (p : Pattern) (ha : d53811 p = 1) (hb : d61358 p = 1) : d61752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2112 q = 1) : d2112 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d61357 q = 1) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2123, d61357, d3433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2124 q = 1) (hb : d61358 q = 1) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d61358, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d61358, d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53792 q = 1) (hb : d61358 q = 1) : d61749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53792, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53793 q = 1) (hb : d61358 q = 1) : d61750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53794 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53795 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53795, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53796 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53796, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d53797 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53798 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53799 q = 1) (hb : d61358 q = 1) : d61751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53799, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53805 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d53806 q = 1) (hb : d61357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53806, d61357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d53807 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53807, d61358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d53808 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d53809 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d53810 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d53811 q = 1) (hb : d61358 q = 1) : d61752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53811, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4836 (p : Pattern) (ha : d53817 p = 1) (hb : d61358 p = 1) : d61758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d61358 q = 1) : d61753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4835 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d61358 q = 1) : d61754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d61358 q = 1) : d61755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d61358 q = 1) : d61756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d61358 q = 1) : d61757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d61358 q = 1) : d61758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4837 (p : Pattern) (ha : d53823 p = 1) (hb : d61358 p = 1) : d61764 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d61358 q = 1) : d61709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4826 q ha hb
    | true =>
      simp only [d53704, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4828 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d61358 q = 1) : d61720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4830 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d61358 q = 1) : d61721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d61358 q = 1) : d61732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4832 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d61358 q = 1) : d61733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d61358 q = 1) : d61734 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d61358 q = 1) : d61745 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4834 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d61358 q = 1) : d61746 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d61358 q = 1) : d61747 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d61358 q = 1) : d61748 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d61358 q = 1) : d61759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4836 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d61358 q = 1) : d61760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d61358 q = 1) : d61761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d61358 q = 1) : d61762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d61358 q = 1) : d61763 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d61358 q = 1) : d61764 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4838 (p : Pattern) (ha : d53829 p = 1) (hb : d61358 p = 1) : d61770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d61358 q = 1) : d61765 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4837 q ha hb
    | true =>
      simp only [d53824, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d61358 q = 1) : d61766 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d61358 q = 1) : d61767 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d61358 q = 1) : d61768 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d61358 q = 1) : d61769 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d61358 q = 1) : d61770 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4839 (p : Pattern) (ha : d53835 p = 1) (hb : d61358 p = 1) : d61776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d61358 q = 1) : d61771 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4838 q ha hb
    | true =>
      simp only [d53830, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d61358 q = 1) : d61772 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d61358 q = 1) : d61773 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d61358 q = 1) : d61774 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d61358 q = 1) : d61775 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d61358 q = 1) : d61776 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4840 (p : Pattern) (ha : d53841 p = 1) (hb : d61358 p = 1) : d61782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d61358 q = 1) : d61777 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4839 q ha hb
    | true =>
      simp only [d53836, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d61358 q = 1) : d61778 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d61358 q = 1) : d61779 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d61358 q = 1) : d61780 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d61358 q = 1) : d61781 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d61358 q = 1) : d61782 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4841 (p : Pattern) (ha : d53847 p = 1) (hb : d61358 p = 1) : d61788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d61358 q = 1) : d61783 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4840 q ha hb
    | true =>
      simp only [d53842, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d61358 q = 1) : d61784 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d61358 q = 1) : d61785 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d61358 q = 1) : d61786 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d61358 q = 1) : d61787 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d61358 q = 1) : d61788 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4842 (p : Pattern) (ha : d53853 p = 1) (hb : d61358 p = 1) : d61794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d61358 q = 1) : d61789 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4841 q ha hb
    | true =>
      simp only [d53848, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d61358 q = 1) : d61790 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d61358 q = 1) : d61791 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d61358 q = 1) : d61792 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d61358 q = 1) : d61793 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d61358 q = 1) : d61794 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4843 (p : Pattern) (ha : d53859 p = 1) (hb : d61358 p = 1) : d61800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d61358 q = 1) : d61795 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4842 q ha hb
    | true =>
      simp only [d53854, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d61358 q = 1) : d61796 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d61358 q = 1) : d61797 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d61358 q = 1) : d61798 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d61358 q = 1) : d61799 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d61358 q = 1) : d61800 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4844 (p : Pattern) (ha : d53865 p = 1) (hb : d61358 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d61358 q = 1) : d61801 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4843 q ha hb
    | true =>
      simp only [d53860, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d61358 q = 1) : d61802 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d61358 q = 1) : d61803 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d61358 q = 1) : d61804 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d61358 q = 1) : d61805 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d61358 q = 1) : d61806 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4845 (p : Pattern) (ha : d60 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4846 (p : Pattern) (ha : d89 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d88 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4847 (p : Pattern) (ha : d95 p = 1) (hb : d72603 p = 1) : d3503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d48 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d56 q = 1) (hb : d72602 q = 1) : d3498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d72602, d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d56, d72602, d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1916 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57 q = 1) (hb : d72603 q = 1) : d3499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d72603, d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57, d72603, d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58 q = 1) (hb : d72603 q = 1) : d3500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58, d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d59 q = 1) (hb : d72603 q = 1) : d3501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4845 q ha hb
  have h8 (q : Pattern) (ha : d62 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d63 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d64 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d65 q = 1) (hb : d72603 q = 1) : d3502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d65, d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d90 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d90, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4846 q ha hb
  have h13 (q : Pattern) (ha : d91 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d91, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d92 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d93 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d95 q = 1) (hb : d72603 q = 1) : d3503 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d95, d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4848 (p : Pattern) (ha : d4349 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4349 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4849 (p : Pattern) (ha : d4359 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4359 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4850 (p : Pattern) (ha : d58614 p = 1) (hb : d72603 p = 1) : d72925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112 q = 1) (hb : d72602 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d72602, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112, d72602, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h5 (q : Pattern) (ha : d113 q = 1) (hb : d72603 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d72603, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113, d72603, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d114 q = 1) (hb : d72603 q = 1) : d3508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51643 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51647 q = 1) (hb : d72602 q = 1) : d62555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d72602, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51647, d72602, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1921 q ha hb
  have h9 (q : Pattern) (ha : d58610 q = 1) (hb : d72603 q = 1) : d72921 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58610, d72603, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58610, d72603, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58611 q = 1) (hb : d72603 q = 1) : d72922 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58611, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58611, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58612 q = 1) (hb : d72603 q = 1) : d72923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58612, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58612, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4350 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4848 q ha hb
  have h14 (q : Pattern) (ha : d4351 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4351, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4352 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4353 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58613 q = 1) (hb : d72603 q = 1) : d72924 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58613, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58613, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4360 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4849 q ha hb
  have h19 (q : Pattern) (ha : d4361 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4361, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4362 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4363 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4364 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58614 q = 1) (hb : d72603 q = 1) : d72925 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58614, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4851 (p : Pattern) (ha : d4385 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4385 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4852 (p : Pattern) (ha : d4395 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4395 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4853 (p : Pattern) (ha : d58624 p = 1) (hb : d72603 p = 1) : d72935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d284 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d292 q = 1) (hb : d72602 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d72602, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d292, d72602, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h5 (q : Pattern) (ha : d293 q = 1) (hb : d72603 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d72603, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293, d72603, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d294 q = 1) (hb : d72603 q = 1) : d3521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51660 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51664 q = 1) (hb : d72602 q = 1) : d62567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d72602, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51664, d72602, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1927 q ha hb
  have h9 (q : Pattern) (ha : d58620 q = 1) (hb : d72603 q = 1) : d72931 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58620, d72603, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58620, d72603, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58621 q = 1) (hb : d72603 q = 1) : d72932 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58621, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58621, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58622 q = 1) (hb : d72603 q = 1) : d72933 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58622, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58622, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4386 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4851 q ha hb
  have h14 (q : Pattern) (ha : d4387 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4387, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4388 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4389 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58623 q = 1) (hb : d72603 q = 1) : d72934 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58623, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58623, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4396 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4852 q ha hb
  have h19 (q : Pattern) (ha : d4397 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4397, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4398 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4399 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4400 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58624 q = 1) (hb : d72603 q = 1) : d72935 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58624, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4854 (p : Pattern) (ha : d58630 p = 1) (hb : d72603 p = 1) : d72941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d72603 q = 1) : d3504 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4847 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d72603 q = 1) : d3505 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d72603 q = 1) : d3506 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d72603 q = 1) : d3507 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58615 q = 1) (hb : d72603 q = 1) : d72926 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58615, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4850 q ha hb
  have h6 (q : Pattern) (ha : d58616 q = 1) (hb : d72603 q = 1) : d72927 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58616, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58617 q = 1) (hb : d72603 q = 1) : d72928 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58617, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58618 q = 1) (hb : d72603 q = 1) : d72929 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58618, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58619 q = 1) (hb : d72603 q = 1) : d72930 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58619, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58625 q = 1) (hb : d72603 q = 1) : d72936 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58625, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4853 q ha hb
  have h11 (q : Pattern) (ha : d58626 q = 1) (hb : d72603 q = 1) : d72937 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58626, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58627 q = 1) (hb : d72603 q = 1) : d72938 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58627, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58628 q = 1) (hb : d72603 q = 1) : d72939 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58628, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58629 q = 1) (hb : d72603 q = 1) : d72940 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58629, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58630 q = 1) (hb : d72603 q = 1) : d72941 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58630, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4855 (p : Pattern) (ha : d4422 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4422 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4856 (p : Pattern) (ha : d4432 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4432 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4857 (p : Pattern) (ha : d58635 p = 1) (hb : d72603 p = 1) : d72946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d508 q = 1) (hb : d72602 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d72602, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d508, d72602, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h5 (q : Pattern) (ha : d509 q = 1) (hb : d72603 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d72603, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d509, d72603, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d510 q = 1) (hb : d72603 q = 1) : d3536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51685 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51689 q = 1) (hb : d72602 q = 1) : d62580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d72602, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51689, d72602, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1935 q ha hb
  have h9 (q : Pattern) (ha : d58631 q = 1) (hb : d72603 q = 1) : d72942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58631, d72603, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58631, d72603, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58632 q = 1) (hb : d72603 q = 1) : d72943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58632, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58632, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58633 q = 1) (hb : d72603 q = 1) : d72944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58633, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58633, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4423 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4855 q ha hb
  have h14 (q : Pattern) (ha : d4424 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4424, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4425 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4426 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58634 q = 1) (hb : d72603 q = 1) : d72945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58634, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58634, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4433 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4856 q ha hb
  have h19 (q : Pattern) (ha : d4434 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4434, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4435 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4436 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4437 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58635 q = 1) (hb : d72603 q = 1) : d72946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58635, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4858 (p : Pattern) (ha : d58641 p = 1) (hb : d72603 p = 1) : d72952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d72603 q = 1) : d72947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4857 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d72603 q = 1) : d72948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d72603 q = 1) : d72949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d72603 q = 1) : d72950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d72603 q = 1) : d72951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d72603 q = 1) : d72952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4859 (p : Pattern) (ha : d4460 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4460 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4860 (p : Pattern) (ha : d4470 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4470 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4861 (p : Pattern) (ha : d58647 p = 1) (hb : d72603 p = 1) : d72958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d789 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d800 q = 1) (hb : d72602 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d72602, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d800, d72602, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h5 (q : Pattern) (ha : d801 q = 1) (hb : d72603 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d72603, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d801, d72603, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d802 q = 1) (hb : d72603 q = 1) : d3553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51711 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51715 q = 1) (hb : d72602 q = 1) : d62594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d72602, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51715, d72602, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1943 q ha hb
  have h9 (q : Pattern) (ha : d58643 q = 1) (hb : d72603 q = 1) : d72954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58643, d72603, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58643, d72603, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58644 q = 1) (hb : d72603 q = 1) : d72955 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58644, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58644, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58645 q = 1) (hb : d72603 q = 1) : d72956 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58645, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58645, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4461 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4859 q ha hb
  have h14 (q : Pattern) (ha : d4462 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4462, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4463 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4464 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58646 q = 1) (hb : d72603 q = 1) : d72957 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58646, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58646, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4471 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4860 q ha hb
  have h19 (q : Pattern) (ha : d4472 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4472, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4473 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4474 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4475 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58647 q = 1) (hb : d72603 q = 1) : d72958 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58647, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4862 (p : Pattern) (ha : d58653 p = 1) (hb : d72603 p = 1) : d72964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d72603 q = 1) : d72959 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4861 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d72603 q = 1) : d72960 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d72603 q = 1) : d72961 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d72603 q = 1) : d72962 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d72603 q = 1) : d72963 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d72603 q = 1) : d72964 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4863 (p : Pattern) (ha : d4499 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4493 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4499 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4864 (p : Pattern) (ha : d4509 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4509 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4865 (p : Pattern) (ha : d58660 p = 1) (hb : d72603 p = 1) : d72971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1179 q = 1) (hb : d72602 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d72602, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1179, d72602, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h5 (q : Pattern) (ha : d1180 q = 1) (hb : d72603 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d72603, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1180, d72603, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1181 q = 1) (hb : d72603 q = 1) : d3571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51738 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51742 q = 1) (hb : d72602 q = 1) : d62609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d72602, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51742, d72602, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1951 q ha hb
  have h9 (q : Pattern) (ha : d58656 q = 1) (hb : d72603 q = 1) : d72967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58656, d72603, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58656, d72603, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58657 q = 1) (hb : d72603 q = 1) : d72968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58657, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58658 q = 1) (hb : d72603 q = 1) : d72969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58658, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4500 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4863 q ha hb
  have h14 (q : Pattern) (ha : d4501 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4501, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4502 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4503 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58659 q = 1) (hb : d72603 q = 1) : d72970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58659, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4510 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4864 q ha hb
  have h19 (q : Pattern) (ha : d4511 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4511, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4512 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4513 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4514 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58660 q = 1) (hb : d72603 q = 1) : d72971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58660, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4866 (p : Pattern) (ha : d58666 p = 1) (hb : d72603 p = 1) : d72977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d72603 q = 1) : d72972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4865 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d72603 q = 1) : d72973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d72603 q = 1) : d72974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d72603 q = 1) : d72975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d72603 q = 1) : d72976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d72603 q = 1) : d72977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4867 (p : Pattern) (ha : d4539 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4533 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4539 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4868 (p : Pattern) (ha : d4549 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4548 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4549 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4869 (p : Pattern) (ha : d58674 p = 1) (hb : d72603 p = 1) : d72985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1629 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1640 q = 1) (hb : d72602 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d72602, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1640, d72602, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h5 (q : Pattern) (ha : d1641 q = 1) (hb : d72603 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d72603, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1641, d72603, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1642 q = 1) (hb : d72603 q = 1) : d3590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51766 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51770 q = 1) (hb : d72602 q = 1) : d62625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d72602, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51770, d72602, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1959 q ha hb
  have h9 (q : Pattern) (ha : d58670 q = 1) (hb : d72603 q = 1) : d72981 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58670, d72603, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58670, d72603, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58671 q = 1) (hb : d72603 q = 1) : d72982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58671, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58672 q = 1) (hb : d72603 q = 1) : d72983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58672, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4540 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4867 q ha hb
  have h14 (q : Pattern) (ha : d4541 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4541, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4542 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4543 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58673 q = 1) (hb : d72603 q = 1) : d72984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58673, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4550 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4868 q ha hb
  have h19 (q : Pattern) (ha : d4551 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4551, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4552 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4553 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4554 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58674 q = 1) (hb : d72603 q = 1) : d72985 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58674, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4870 (p : Pattern) (ha : d58680 p = 1) (hb : d72603 p = 1) : d72991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d72603 q = 1) : d72986 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4869 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d72603 q = 1) : d72987 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d72603 q = 1) : d72988 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d72603 q = 1) : d72989 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d72603 q = 1) : d72990 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d72603 q = 1) : d72991 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4871 (p : Pattern) (ha : d4580 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4580 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4872 (p : Pattern) (ha : d4590 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4589 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4590 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4873 (p : Pattern) (ha : d58689 p = 1) (hb : d72603 p = 1) : d73000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2112 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2123 q = 1) (hb : d72602 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d72602, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2123, d72602, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h5 (q : Pattern) (ha : d2124 q = 1) (hb : d72603 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d72603, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2124, d72603, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2125 q = 1) (hb : d72603 q = 1) : d3610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51795 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51799 q = 1) (hb : d72602 q = 1) : d62642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d72602, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d51799, d72602, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1967 q ha hb
  have h9 (q : Pattern) (ha : d58685 q = 1) (hb : d72603 q = 1) : d72996 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58685, d72603, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58685, d72603, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d58686 q = 1) (hb : d72603 q = 1) : d72997 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58686, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58686, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58687 q = 1) (hb : d72603 q = 1) : d72998 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58687, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58687, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4581 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4871 q ha hb
  have h14 (q : Pattern) (ha : d4582 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4582, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4583 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d4584 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d58688 q = 1) (hb : d72603 q = 1) : d72999 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58688, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58688, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4591 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4872 q ha hb
  have h19 (q : Pattern) (ha : d4592 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4592, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4593 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h21 (q : Pattern) (ha : d4594 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h22 (q : Pattern) (ha : d4595 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d58689 q = 1) (hb : d72603 q = 1) : d73000 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d58689, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4874 (p : Pattern) (ha : d58695 p = 1) (hb : d72603 p = 1) : d73006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d72603 q = 1) : d73001 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4873 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d72603 q = 1) : d73002 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d72603 q = 1) : d73003 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d72603 q = 1) : d73004 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d72603 q = 1) : d73005 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d72603 q = 1) : d73006 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4875 (p : Pattern) (ha : d58701 p = 1) (hb : d72603 p = 1) : d73012 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d72603 q = 1) : d72953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4854 q ha hb
    | true =>
      simp only [d58642, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4858 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d72603 q = 1) : d72965 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4862 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d72603 q = 1) : d72966 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d72603 q = 1) : d72978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4866 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d72603 q = 1) : d72979 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d72603 q = 1) : d72980 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d72603 q = 1) : d72992 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4870 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d72603 q = 1) : d72993 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d72603 q = 1) : d72994 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d72603 q = 1) : d72995 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d72603 q = 1) : d73007 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4874 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d72603 q = 1) : d73008 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d72603 q = 1) : d73009 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d72603 q = 1) : d73010 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d72603 q = 1) : d73011 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d72603 q = 1) : d73012 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4876 (p : Pattern) (ha : d58707 p = 1) (hb : d72603 p = 1) : d73018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d72603 q = 1) : d73013 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4875 q ha hb
    | true =>
      simp only [d58702, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d72603 q = 1) : d73014 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d72603 q = 1) : d73015 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d72603 q = 1) : d73016 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d72603 q = 1) : d73017 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d72603 q = 1) : d73018 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4877 (p : Pattern) (ha : d58713 p = 1) (hb : d72603 p = 1) : d73024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d72603 q = 1) : d73019 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4876 q ha hb
    | true =>
      simp only [d58708, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d72603 q = 1) : d73020 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d72603 q = 1) : d73021 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d72603 q = 1) : d73022 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d72603 q = 1) : d73023 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d72603 q = 1) : d73024 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4878 (p : Pattern) (ha : d58719 p = 1) (hb : d72603 p = 1) : d73030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d72603 q = 1) : d73025 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4877 q ha hb
    | true =>
      simp only [d58714, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d72603 q = 1) : d73026 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d72603 q = 1) : d73027 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d72603 q = 1) : d73028 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d72603 q = 1) : d73029 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d72603 q = 1) : d73030 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4879 (p : Pattern) (ha : d58725 p = 1) (hb : d72603 p = 1) : d73036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d72603 q = 1) : d73031 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4878 q ha hb
    | true =>
      simp only [d58720, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d72603 q = 1) : d73032 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d72603 q = 1) : d73033 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d72603 q = 1) : d73034 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d72603 q = 1) : d73035 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d72603 q = 1) : d73036 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4880 (p : Pattern) (ha : d58731 p = 1) (hb : d72603 p = 1) : d73042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d72603 q = 1) : d73037 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4879 q ha hb
    | true =>
      simp only [d58726, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d72603 q = 1) : d73038 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d72603 q = 1) : d73039 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d72603 q = 1) : d73040 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d72603 q = 1) : d73041 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d72603 q = 1) : d73042 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4881 (p : Pattern) (ha : d58737 p = 1) (hb : d72603 p = 1) : d73048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d72603 q = 1) : d73043 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4880 q ha hb
    | true =>
      simp only [d58732, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d72603 q = 1) : d73044 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d72603 q = 1) : d73045 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d72603 q = 1) : d73046 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58736 q = 1) (hb : d72603 q = 1) : d73047 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58737 q = 1) (hb : d72603 q = 1) : d73048 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58737, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4882 (p : Pattern) (ha : d58743 p = 1) (hb : d72603 p = 1) : d73054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d72603 q = 1) : d73049 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4881 q ha hb
    | true =>
      simp only [d58738, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d72603 q = 1) : d73050 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d72603 q = 1) : d73051 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d72603 q = 1) : d73052 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d72603 q = 1) : d73053 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d72603 q = 1) : d73054 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4883 (p : Pattern) (ha : d3497 p = 1) (hb : d51899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d51897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d51898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3497 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4884 (p : Pattern) (ha : d3503 p = 1) (hb : d72768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3498 q = 1) (hb : d51899 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4883 q ha hb
  have h3 (q : Pattern) (ha : d3499 q = 1) (hb : d72764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, d72764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3499, d72764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3500 q = 1) (hb : d72765 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, d72765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3500, d72765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3501 q = 1) (hb : d72766 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, d72766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, d72766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3502 q = 1) (hb : d72767 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d72767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3502, d72767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d3503 q = 1) (hb : d72768 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, d72768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3503, d72768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro4885 (p : Pattern) (ha : d52012 p = 1) (hb : d62554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4335 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4336 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4336, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51641 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51642 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52012 q = 1) (hb : d62554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4886 (p : Pattern) (ha : d72779 p = 1) (hb : d72925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro644 q ha hb
  have h3 (q : Pattern) (ha : d2526 q = 1) (hb : d72773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d72773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d72773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3508 q = 1) (hb : d72774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d72774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, d72774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52012 q = 1) (hb : d62555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4885 q ha hb
  have h7 (q : Pattern) (ha : d72775 q = 1) (hb : d72921 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72775, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72775, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d72776 q = 1) (hb : d72922 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72776, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d72776, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d72777 q = 1) (hb : d72923 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72777, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72777, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72778 q = 1) (hb : d72924 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72778, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72778, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d72779 q = 1) (hb : d72925 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72779, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72779, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro4887 (p : Pattern) (ha : d52142 p = 1) (hb : d62566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51 q ha hb
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4372 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51658 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51658, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51659 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52142 q = 1) (hb : d62566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4888 (p : Pattern) (ha : d72791 p = 1) (hb : d72935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro646 q ha hb
  have h3 (q : Pattern) (ha : d2538 q = 1) (hb : d72785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d72785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d72785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3521 q = 1) (hb : d72786 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d72786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, d72786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52142 q = 1) (hb : d62567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4887 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72787 q = 1) (hb : d72931 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72787, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72787, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72788 q = 1) (hb : d72932 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72788, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72788, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72789 q = 1) (hb : d72933 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72789, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72789, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72790 q = 1) (hb : d72934 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72790, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72790, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72791 q = 1) (hb : d72935 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72791, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72791, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4889 (p : Pattern) (ha : d72797 p = 1) (hb : d72941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d72769 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, d72769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, d72769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4884 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d72770 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, d72770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, d72770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d72771 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, d72771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, d72771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d72772 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, d72772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, d72772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72780 q = 1) (hb : d72926 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72780, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72780, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4886 q ha hb
  have h6 (q : Pattern) (ha : d72781 q = 1) (hb : d72927 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72781, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72781, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72782 q = 1) (hb : d72928 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72782, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72782, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72783 q = 1) (hb : d72929 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72783, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72783, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72784 q = 1) (hb : d72930 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72784, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72784, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72792 q = 1) (hb : d72936 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72792, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72792, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4888 q ha hb
  have h11 (q : Pattern) (ha : d72793 q = 1) (hb : d72937 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72793, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72793, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72794 q = 1) (hb : d72938 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72794, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72794, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d72795 q = 1) (hb : d72939 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72795, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72795, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d72796 q = 1) (hb : d72940 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72796, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72796, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72797 q = 1) (hb : d72941 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72797, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72797, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4890 (p : Pattern) (ha : d52314 p = 1) (hb : d62579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87 q ha hb
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4408 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4409 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4409, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51683 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51683, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51684 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52314 q = 1) (hb : d62579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4891 (p : Pattern) (ha : d72804 p = 1) (hb : d72946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro649 q ha hb
  have h3 (q : Pattern) (ha : d2551 q = 1) (hb : d72798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d72798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d72798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3536 q = 1) (hb : d72799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d72799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, d72799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52314 q = 1) (hb : d62580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4890 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72800 q = 1) (hb : d72942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72800, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72800, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72801 q = 1) (hb : d72943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72801, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72801, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72802 q = 1) (hb : d72944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72802, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72802, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72803 q = 1) (hb : d72945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72803, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72803, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72804 q = 1) (hb : d72946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72804, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72804, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4892 (p : Pattern) (ha : d72810 p = 1) (hb : d72952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72805 q = 1) (hb : d72947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72805, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72805, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4891 q ha hb
  have h2 (q : Pattern) (ha : d72806 q = 1) (hb : d72948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72806, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72806, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72807 q = 1) (hb : d72949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72807, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72807, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72808 q = 1) (hb : d72950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72808, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72808, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72809 q = 1) (hb : d72951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72809, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72809, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72810 q = 1) (hb : d72952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72810, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72810, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4893 (p : Pattern) (ha : d52535 p = 1) (hb : d62593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro134 q ha hb
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4447 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4447, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51709 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51709, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51710 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52535 q = 1) (hb : d62593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4894 (p : Pattern) (ha : d72818 p = 1) (hb : d72958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro652 q ha hb
  have h3 (q : Pattern) (ha : d2565 q = 1) (hb : d72812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d72812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d72812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3553 q = 1) (hb : d72813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d72813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, d72813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52535 q = 1) (hb : d62594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4893 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72814 q = 1) (hb : d72954 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72814, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72814, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72815 q = 1) (hb : d72955 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72815, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72815, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72816 q = 1) (hb : d72956 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72816, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72816, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72817 q = 1) (hb : d72957 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72817, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72817, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72818 q = 1) (hb : d72958 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72818, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72818, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4895 (p : Pattern) (ha : d72824 p = 1) (hb : d72964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72819 q = 1) (hb : d72959 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72819, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72819, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4894 q ha hb
  have h2 (q : Pattern) (ha : d72820 q = 1) (hb : d72960 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72820, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72820, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72821 q = 1) (hb : d72961 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72821, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72821, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72822 q = 1) (hb : d72962 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72822, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72822, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72823 q = 1) (hb : d72963 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72823, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72823, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72824 q = 1) (hb : d72964 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72824, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72824, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4896 (p : Pattern) (ha : d52815 p = 1) (hb : d62608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro186 q ha hb
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4486 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4486, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51736 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51736, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51737 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52815 q = 1) (hb : d62608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4897 (p : Pattern) (ha : d72833 p = 1) (hb : d72971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro655 q ha hb
  have h3 (q : Pattern) (ha : d2580 q = 1) (hb : d72827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d72827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d72827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3571 q = 1) (hb : d72828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d72828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, d72828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52815 q = 1) (hb : d62609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4896 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72829 q = 1) (hb : d72967 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72829, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72829, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72830 q = 1) (hb : d72968 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72830, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72830, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72831 q = 1) (hb : d72969 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72831, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72831, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72832 q = 1) (hb : d72970 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72832, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72832, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72833 q = 1) (hb : d72971 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72833, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72833, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4898 (p : Pattern) (ha : d72839 p = 1) (hb : d72977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72834 q = 1) (hb : d72972 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72834, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72834, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4897 q ha hb
  have h2 (q : Pattern) (ha : d72835 q = 1) (hb : d72973 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72835, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72835, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72836 q = 1) (hb : d72974 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72836, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72836, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72837 q = 1) (hb : d72975 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72837, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72837, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72838 q = 1) (hb : d72976 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72838, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72838, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72839 q = 1) (hb : d72977 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72839, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72839, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4899 (p : Pattern) (ha : d53130 p = 1) (hb : d62624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro242 q ha hb
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4526 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4526, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51764 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51764, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51765 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53130 q = 1) (hb : d62624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4900 (p : Pattern) (ha : d72849 p = 1) (hb : d72985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro658 q ha hb
  have h3 (q : Pattern) (ha : d2596 q = 1) (hb : d72843 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d72843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d72843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3590 q = 1) (hb : d72844 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d72844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, d72844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53130 q = 1) (hb : d62625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4899 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72845 q = 1) (hb : d72981 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72845, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72845, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72846 q = 1) (hb : d72982 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72846, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72846, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72847 q = 1) (hb : d72983 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72847, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72847, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72848 q = 1) (hb : d72984 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72848, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72848, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72849 q = 1) (hb : d72985 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72849, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72849, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4901 (p : Pattern) (ha : d72855 p = 1) (hb : d72991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72850 q = 1) (hb : d72986 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72850, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72850, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4900 q ha hb
  have h2 (q : Pattern) (ha : d72851 q = 1) (hb : d72987 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72851, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72851, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72852 q = 1) (hb : d72988 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72852, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72852, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72853 q = 1) (hb : d72989 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72853, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72853, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72854 q = 1) (hb : d72990 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72854, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72854, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72855 q = 1) (hb : d72991 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72855, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72855, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4902 (p : Pattern) (ha : d53447 p = 1) (hb : d62641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro301 q ha hb
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4567 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51793 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51794 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53447 q = 1) (hb : d62641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro4903 (p : Pattern) (ha : d72866 p = 1) (hb : d73000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro661 q ha hb
  have h3 (q : Pattern) (ha : d2613 q = 1) (hb : d72860 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d72860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d72860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3610 q = 1) (hb : d72861 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d72861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d72861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53447 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4902 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72862 q = 1) (hb : d72996 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72862, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72862, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d72863 q = 1) (hb : d72997 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72863, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72863, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d72864 q = 1) (hb : d72998 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72864, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d72864, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72865 q = 1) (hb : d72999 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72865, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72865, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d72866 q = 1) (hb : d73000 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72866, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72866, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro4904 (p : Pattern) (ha : d72872 p = 1) (hb : d73006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72867 q = 1) (hb : d73001 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72867, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72867, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4903 q ha hb
  have h2 (q : Pattern) (ha : d72868 q = 1) (hb : d73002 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72868, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72868, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72869 q = 1) (hb : d73003 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72869, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72869, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72870 q = 1) (hb : d73004 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72870, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72870, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72871 q = 1) (hb : d73005 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72871, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72871, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72872 q = 1) (hb : d73006 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72872, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d72872, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4905 (p : Pattern) (ha : d72878 p = 1) (hb : d73012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d72811 q = 1) (hb : d72953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72811, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4889 q ha hb
    | true =>
      simp only [d72811, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4892 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72825 q = 1) (hb : d72965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72825, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72825, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4895 q ha hb
  have h3 (q : Pattern) (ha : d72826 q = 1) (hb : d72966 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72826, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72826, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72840 q = 1) (hb : d72978 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72840, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72840, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4898 q ha hb
  have h5 (q : Pattern) (ha : d72841 q = 1) (hb : d72979 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72841, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72841, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72842 q = 1) (hb : d72980 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72842, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72842, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72856 q = 1) (hb : d72992 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72856, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72856, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4901 q ha hb
  have h8 (q : Pattern) (ha : d72857 q = 1) (hb : d72993 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72857, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72857, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72858 q = 1) (hb : d72994 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72858, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72858, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72859 q = 1) (hb : d72995 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72859, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72859, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72873 q = 1) (hb : d73007 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72873, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72873, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4904 q ha hb
  have h12 (q : Pattern) (ha : d72874 q = 1) (hb : d73008 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72874, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72874, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d72875 q = 1) (hb : d73009 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72875, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72875, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d72876 q = 1) (hb : d73010 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72876, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72876, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72877 q = 1) (hb : d73011 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d72877, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72877, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d72878 q = 1) (hb : d73012 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d72878, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72878, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4906 (p : Pattern) (ha : d72884 p = 1) (hb : d73018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72879 q = 1) (hb : d73013 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d72879, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4905 q ha hb
    | true =>
      simp only [d72879, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72880 q = 1) (hb : d73014 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d72880, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72880, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72881 q = 1) (hb : d73015 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d72881, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72881, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72882 q = 1) (hb : d73016 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d72882, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72882, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72883 q = 1) (hb : d73017 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d72883, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72883, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72884 q = 1) (hb : d73018 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d72884, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72884, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4907 (p : Pattern) (ha : d72890 p = 1) (hb : d73024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72885 q = 1) (hb : d73019 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d72885, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4906 q ha hb
    | true =>
      simp only [d72885, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72886 q = 1) (hb : d73020 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d72886, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72886, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72887 q = 1) (hb : d73021 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d72887, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72887, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72888 q = 1) (hb : d73022 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d72888, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72888, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72889 q = 1) (hb : d73023 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d72889, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72889, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72890 q = 1) (hb : d73024 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d72890, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72890, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4908 (p : Pattern) (ha : d72896 p = 1) (hb : d73030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72891 q = 1) (hb : d73025 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d72891, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4907 q ha hb
    | true =>
      simp only [d72891, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72892 q = 1) (hb : d73026 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d72892, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72892, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72893 q = 1) (hb : d73027 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d72893, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72893, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72894 q = 1) (hb : d73028 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d72894, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72894, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72895 q = 1) (hb : d73029 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d72895, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72895, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72896 q = 1) (hb : d73030 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d72896, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72896, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4909 (p : Pattern) (ha : d72902 p = 1) (hb : d73036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72897 q = 1) (hb : d73031 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d72897, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4908 q ha hb
    | true =>
      simp only [d72897, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72898 q = 1) (hb : d73032 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d72898, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72898, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72899 q = 1) (hb : d73033 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d72899, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72899, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72900 q = 1) (hb : d73034 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d72900, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72900, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72901 q = 1) (hb : d73035 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d72901, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72901, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72902 q = 1) (hb : d73036 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d72902, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72902, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4910 (p : Pattern) (ha : d72908 p = 1) (hb : d73042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72903 q = 1) (hb : d73037 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d72903, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4909 q ha hb
    | true =>
      simp only [d72903, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72904 q = 1) (hb : d73038 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d72904, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72904, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72905 q = 1) (hb : d73039 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d72905, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72905, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72906 q = 1) (hb : d73040 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d72906, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72906, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72907 q = 1) (hb : d73041 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d72907, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72907, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72908 q = 1) (hb : d73042 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d72908, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72908, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4911 (p : Pattern) (ha : d72914 p = 1) (hb : d73048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72909 q = 1) (hb : d73043 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d72909, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4910 q ha hb
    | true =>
      simp only [d72909, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72910 q = 1) (hb : d73044 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d72910, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72910, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72911 q = 1) (hb : d73045 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d72911, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72911, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72912 q = 1) (hb : d73046 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d72912, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72912, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72913 q = 1) (hb : d73047 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d72913, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72913, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72914 q = 1) (hb : d73048 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d72914, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72914, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4912 (p : Pattern) (ha : d72920 p = 1) (hb : d73054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72915 q = 1) (hb : d73049 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d72915, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4911 q ha hb
    | true =>
      simp only [d72915, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d72916 q = 1) (hb : d73050 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d72916, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72916, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d72917 q = 1) (hb : d73051 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d72917, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72917, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d72918 q = 1) (hb : d73052 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d72918, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72918, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72919 q = 1) (hb : d73053 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d72919, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72919, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d72920 q = 1) (hb : d73054 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d72920, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72920, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4913 (p : Pattern) (ha : d406 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d406 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4914 (p : Pattern) (ha : d462 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d462 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4915 (p : Pattern) (ha : d53647 p = 1) (hb : d72603 p = 1) : d62704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112 q = 1) (hb : d72602 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d72602, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112, d72602, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d72603 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d72603, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113, d72603, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d72603 q = 1) : d2527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53637, d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d72603 q = 1) : d62702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d407, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4913 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d72603 q = 1) : d62703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d463, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4914 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d72603 q = 1) : d62704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4916 (p : Pattern) (ha : d53655 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53655 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4917 (p : Pattern) (ha : d53665 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53665 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4918 (p : Pattern) (ha : d53671 p = 1) (hb : d72603 p = 1) : d62712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292 q = 1) (hb : d72602 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d72602, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292, d72602, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d72603 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d72603, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293, d72603, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53653 q = 1) (hb : d72603 q = 1) : d2539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53653, d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53654 q = 1) (hb : d72603 q = 1) : d62710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53656 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53656, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4916 q ha hb
  have h8 (q : Pattern) (ha : d53657 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53657, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53658 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53659 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53660 q = 1) (hb : d72603 q = 1) : d62711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53660, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53666 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53666, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4917 q ha hb
  have h13 (q : Pattern) (ha : d53667 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53667, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53668 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53669 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53670 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53671 q = 1) (hb : d72603 q = 1) : d62712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53671, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4919 (p : Pattern) (ha : d53677 p = 1) (hb : d72603 p = 1) : d62718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d72603 q = 1) : d62705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4915 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d72603 q = 1) : d62706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d72603 q = 1) : d62707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d72603 q = 1) : d62708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d72603 q = 1) : d62709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d72603 q = 1) : d62713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4918 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d72603 q = 1) : d62714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d72603 q = 1) : d62715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d72603 q = 1) : d62716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d72603 q = 1) : d62717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d72603 q = 1) : d62718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4920 (p : Pattern) (ha : d53680 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53680 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4921 (p : Pattern) (ha : d53691 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53691 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4922 (p : Pattern) (ha : d53697 p = 1) (hb : d72603 p = 1) : d62721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d508 q = 1) (hb : d72602 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d72602, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d508, d72602, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d72603 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d72603, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d509, d72603, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53678 q = 1) (hb : d72603 q = 1) : d2552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53678, d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53679 q = 1) (hb : d72603 q = 1) : d62719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53681 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53681, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4920 q ha hb
  have h8 (q : Pattern) (ha : d53682 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53682, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53683 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53684 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53685 q = 1) (hb : d72603 q = 1) : d62720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53685, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53692 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53692, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4921 q ha hb
  have h13 (q : Pattern) (ha : d53693 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53693, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53694 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53695 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53696 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53697 q = 1) (hb : d72603 q = 1) : d62721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53697, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4923 (p : Pattern) (ha : d53703 p = 1) (hb : d72603 p = 1) : d62727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d72603 q = 1) : d62722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4922 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d72603 q = 1) : d62723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d72603 q = 1) : d62724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d72603 q = 1) : d62725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d72603 q = 1) : d62726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d72603 q = 1) : d62727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4924 (p : Pattern) (ha : d53707 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53707 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4925 (p : Pattern) (ha : d53718 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53718 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4926 (p : Pattern) (ha : d53724 p = 1) (hb : d72603 p = 1) : d62731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d800 q = 1) (hb : d72602 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d72602, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d800, d72602, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d72603 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d72603, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d801, d72603, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53705 q = 1) (hb : d72603 q = 1) : d2566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53705, d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53706 q = 1) (hb : d72603 q = 1) : d62729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53708 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53708, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4924 q ha hb
  have h8 (q : Pattern) (ha : d53709 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53709, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53710 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53711 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53712 q = 1) (hb : d72603 q = 1) : d62730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53712, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53719 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53719, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4925 q ha hb
  have h13 (q : Pattern) (ha : d53720 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53720, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53721 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53722 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53723 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53724 q = 1) (hb : d72603 q = 1) : d62731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53724, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4927 (p : Pattern) (ha : d53730 p = 1) (hb : d72603 p = 1) : d62737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d72603 q = 1) : d62732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4926 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d72603 q = 1) : d62733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d72603 q = 1) : d62734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d72603 q = 1) : d62735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d72603 q = 1) : d62736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d72603 q = 1) : d62737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4928 (p : Pattern) (ha : d53735 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53735 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4929 (p : Pattern) (ha : d53746 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53745 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53746 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4930 (p : Pattern) (ha : d53752 p = 1) (hb : d72603 p = 1) : d62742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1179 q = 1) (hb : d72602 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d72602, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1179, d72602, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d72603 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d72603, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1180, d72603, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53733 q = 1) (hb : d72603 q = 1) : d2581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53733, d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53734 q = 1) (hb : d72603 q = 1) : d62740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53736 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53736, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4928 q ha hb
  have h8 (q : Pattern) (ha : d53737 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53737, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53738 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53739 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53740 q = 1) (hb : d72603 q = 1) : d62741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53740, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53747 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53747, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4929 q ha hb
  have h13 (q : Pattern) (ha : d53748 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53748, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53749 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53750 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53751 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53752 q = 1) (hb : d72603 q = 1) : d62742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53752, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4931 (p : Pattern) (ha : d53758 p = 1) (hb : d72603 p = 1) : d62748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d72603 q = 1) : d62743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4930 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d72603 q = 1) : d62744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d72603 q = 1) : d62745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d72603 q = 1) : d62746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d72603 q = 1) : d62747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d72603 q = 1) : d62748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4932 (p : Pattern) (ha : d53764 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1638 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53764 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4933 (p : Pattern) (ha : d53775 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53775 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4934 (p : Pattern) (ha : d53781 p = 1) (hb : d72603 p = 1) : d62754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1640 q = 1) (hb : d72602 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d72602, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1640, d72602, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d72603 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d72603, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1641, d72603, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53762 q = 1) (hb : d72603 q = 1) : d2597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53762, d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53763 q = 1) (hb : d72603 q = 1) : d62752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53765 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53765, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4932 q ha hb
  have h8 (q : Pattern) (ha : d53766 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53766, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53767 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53768 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53769 q = 1) (hb : d72603 q = 1) : d62753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53769, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53776 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53776, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4933 q ha hb
  have h13 (q : Pattern) (ha : d53777 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53777, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53778 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53779 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53780 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53781 q = 1) (hb : d72603 q = 1) : d62754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53781, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4935 (p : Pattern) (ha : d53787 p = 1) (hb : d72603 p = 1) : d62760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d72603 q = 1) : d62755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4934 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d72603 q = 1) : d62756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d72603 q = 1) : d62757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d72603 q = 1) : d62758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d72603 q = 1) : d62759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d72603 q = 1) : d62760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4936 (p : Pattern) (ha : d53794 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53794 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4937 (p : Pattern) (ha : d53805 p = 1) (hb : d54978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53805 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d54978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro4938 (p : Pattern) (ha : d53811 p = 1) (hb : d72603 p = 1) : d62767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2123 q = 1) (hb : d72602 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d72602, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2123, d72602, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d72603 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d72603, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2124, d72603, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53792 q = 1) (hb : d72603 q = 1) : d2614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53792, d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53793 q = 1) (hb : d72603 q = 1) : d62765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53795 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53795, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4936 q ha hb
  have h8 (q : Pattern) (ha : d53796 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53796, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d53797 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53798 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53799 q = 1) (hb : d72603 q = 1) : d62766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53799, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53806 q = 1) (hb : d72602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53806, d72602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4937 q ha hb
  have h13 (q : Pattern) (ha : d53807 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53807, d72603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d53808 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53809 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53810 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53811 q = 1) (hb : d72603 q = 1) : d62767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53811, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro4939 (p : Pattern) (ha : d53817 p = 1) (hb : d72603 p = 1) : d62773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d72603 q = 1) : d62768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4938 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d72603 q = 1) : d62769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d72603 q = 1) : d62770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d72603 q = 1) : d62771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d72603 q = 1) : d62772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d72603 q = 1) : d62773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4940 (p : Pattern) (ha : d53823 p = 1) (hb : d72603 p = 1) : d62779 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d72603 q = 1) : d62728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4919 q ha hb
    | true =>
      simp only [d53704, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4923 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d72603 q = 1) : d62738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4927 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d72603 q = 1) : d62739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d72603 q = 1) : d62749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4931 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d72603 q = 1) : d62750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d72603 q = 1) : d62751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d72603 q = 1) : d62761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4935 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d72603 q = 1) : d62762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d72603 q = 1) : d62763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d72603 q = 1) : d62764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d72603 q = 1) : d62774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4939 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d72603 q = 1) : d62775 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d72603 q = 1) : d62776 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d72603 q = 1) : d62777 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d72603 q = 1) : d62778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d72603 q = 1) : d62779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4941 (p : Pattern) (ha : d53829 p = 1) (hb : d72603 p = 1) : d62785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d72603 q = 1) : d62780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4940 q ha hb
    | true =>
      simp only [d53824, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d72603 q = 1) : d62781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d72603 q = 1) : d62782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d72603 q = 1) : d62783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d72603 q = 1) : d62784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d72603 q = 1) : d62785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4942 (p : Pattern) (ha : d53835 p = 1) (hb : d72603 p = 1) : d62791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d72603 q = 1) : d62786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4941 q ha hb
    | true =>
      simp only [d53830, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d72603 q = 1) : d62787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d72603 q = 1) : d62788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d72603 q = 1) : d62789 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d72603 q = 1) : d62790 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d72603 q = 1) : d62791 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4943 (p : Pattern) (ha : d53841 p = 1) (hb : d72603 p = 1) : d62797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d72603 q = 1) : d62792 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4942 q ha hb
    | true =>
      simp only [d53836, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d72603 q = 1) : d62793 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d72603 q = 1) : d62794 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d72603 q = 1) : d62795 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d72603 q = 1) : d62796 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d72603 q = 1) : d62797 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4944 (p : Pattern) (ha : d53847 p = 1) (hb : d72603 p = 1) : d62803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d72603 q = 1) : d62798 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4943 q ha hb
    | true =>
      simp only [d53842, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d72603 q = 1) : d62799 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d72603 q = 1) : d62800 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d72603 q = 1) : d62801 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d72603 q = 1) : d62802 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d72603 q = 1) : d62803 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4945 (p : Pattern) (ha : d53853 p = 1) (hb : d72603 p = 1) : d62809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d72603 q = 1) : d62804 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4944 q ha hb
    | true =>
      simp only [d53848, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d72603 q = 1) : d62805 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d72603 q = 1) : d62806 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d72603 q = 1) : d62807 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d72603 q = 1) : d62808 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d72603 q = 1) : d62809 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4946 (p : Pattern) (ha : d53859 p = 1) (hb : d72603 p = 1) : d62815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d72603 q = 1) : d62810 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4945 q ha hb
    | true =>
      simp only [d53854, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d72603 q = 1) : d62811 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d72603 q = 1) : d62812 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d72603 q = 1) : d62813 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d72603 q = 1) : d62814 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d72603 q = 1) : d62815 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4947 (p : Pattern) (ha : d53865 p = 1) (hb : d72603 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d72603 q = 1) : d62816 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4946 q ha hb
    | true =>
      simp only [d53860, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d72603 q = 1) : d62817 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d72603 q = 1) : d62818 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d72603 q = 1) : d62819 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d72603 q = 1) : d62820 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d72603 q = 1) : d62821 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4948 (p : Pattern) (ha : d213 p = 1) (hb : d52012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d213 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4949 (p : Pattern) (ha : d62704 p = 1) (hb : d72779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4948 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d72775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d72775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d72775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2527 q = 1) (hb : d72776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d72776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d72776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d62702 q = 1) (hb : d72777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, d72777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, d72777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62703 q = 1) (hb : d72778 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, d72778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62703, d72778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d62704 q = 1) (hb : d72779 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, d72779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62704, d72779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h8 p ha hb
theorem andIntro4950 (p : Pattern) (ha : d2536 p = 1) (hb : d52142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4951 (p : Pattern) (ha : d62712 p = 1) (hb : d72791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72786 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4950 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d72787 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d72787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d72787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2539 q = 1) (hb : d72788 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d72788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d72788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62710 q = 1) (hb : d72789 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, d72789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, d72789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62711 q = 1) (hb : d72790 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, d72790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62711, d72790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62712 q = 1) (hb : d72791 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, d72791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62712, d72791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4952 (p : Pattern) (ha : d62718 p = 1) (hb : d72797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62705 q = 1) (hb : d72780 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, d72780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62705, d72780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4949 q ha hb
  have h3 (q : Pattern) (ha : d62706 q = 1) (hb : d72781 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, d72781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62706, d72781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62707 q = 1) (hb : d72782 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, d72782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62707, d72782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62708 q = 1) (hb : d72783 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, d72783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62708, d72783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62709 q = 1) (hb : d72784 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, d72784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, d72784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62713 q = 1) (hb : d72792 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, d72792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62713, d72792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4951 q ha hb
  have h8 (q : Pattern) (ha : d62714 q = 1) (hb : d72793 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, d72793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62714, d72793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62715 q = 1) (hb : d72794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, d72794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62715, d72794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62716 q = 1) (hb : d72795 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, d72795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62716, d72795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62717 q = 1) (hb : d72796 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, d72796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62717, d72796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62718 q = 1) (hb : d72797 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, d72797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62718, d72797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro4953 (p : Pattern) (ha : d2549 p = 1) (hb : d52314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4954 (p : Pattern) (ha : d62721 p = 1) (hb : d72804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72799 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4953 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d72800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d72800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d72800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2552 q = 1) (hb : d72801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d72801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d72801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62719 q = 1) (hb : d72802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, d72802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, d72802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62720 q = 1) (hb : d72803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, d72803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62720, d72803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62721 q = 1) (hb : d72804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, d72804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62721, d72804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4955 (p : Pattern) (ha : d62727 p = 1) (hb : d72810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d72805 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, d72805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, d72805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4954 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d72806 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, d72806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, d72806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d72807 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, d72807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, d72807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d72808 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, d72808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, d72808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d72809 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, d72809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, d72809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d72810 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, d72810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, d72810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4956 (p : Pattern) (ha : d2563 p = 1) (hb : d52535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4957 (p : Pattern) (ha : d62731 p = 1) (hb : d72818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72813 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4956 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d72814 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d72814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d72814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2566 q = 1) (hb : d72815 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d72815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d72815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62729 q = 1) (hb : d72816 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, d72816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, d72816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62730 q = 1) (hb : d72817 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, d72817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62730, d72817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62731 q = 1) (hb : d72818 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, d72818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62731, d72818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4958 (p : Pattern) (ha : d62737 p = 1) (hb : d72824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d72819 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, d72819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, d72819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4957 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d72820 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, d72820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, d72820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d72821 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, d72821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, d72821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d72822 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, d72822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, d72822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d72823 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, d72823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, d72823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d72824 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, d72824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, d72824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4959 (p : Pattern) (ha : d2578 p = 1) (hb : d52815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4960 (p : Pattern) (ha : d62742 p = 1) (hb : d72833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72828 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4959 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d72829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d72829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d72829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2581 q = 1) (hb : d72830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d72830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d72830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62740 q = 1) (hb : d72831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, d72831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, d72831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62741 q = 1) (hb : d72832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, d72832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62741, d72832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62742 q = 1) (hb : d72833 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, d72833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62742, d72833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4961 (p : Pattern) (ha : d62748 p = 1) (hb : d72839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d72834 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, d72834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, d72834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4960 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d72835 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, d72835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, d72835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d72836 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, d72836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, d72836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d72837 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, d72837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, d72837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d72838 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, d72838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, d72838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d72839 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, d72839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, d72839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4962 (p : Pattern) (ha : d2594 p = 1) (hb : d53130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4963 (p : Pattern) (ha : d62754 p = 1) (hb : d72849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4962 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d72845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d72845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d72845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2597 q = 1) (hb : d72846 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d72846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d72846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62752 q = 1) (hb : d72847 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, d72847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, d72847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62753 q = 1) (hb : d72848 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, d72848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62753, d72848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62754 q = 1) (hb : d72849 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, d72849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62754, d72849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4964 (p : Pattern) (ha : d62760 p = 1) (hb : d72855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d72850 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, d72850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, d72850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4963 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d72851 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, d72851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, d72851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d72852 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, d72852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, d72852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d72853 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, d72853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, d72853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d72854 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, d72854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, d72854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d72855 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, d72855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, d72855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4965 (p : Pattern) (ha : d2611 p = 1) (hb : d53447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4966 (p : Pattern) (ha : d62767 p = 1) (hb : d72866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4965 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d72862 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d72862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d72862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2614 q = 1) (hb : d72863 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d72863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d72863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62765 q = 1) (hb : d72864 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, d72864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, d72864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62766 q = 1) (hb : d72865 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, d72865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62766, d72865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62767 q = 1) (hb : d72866 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, d72866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62767, d72866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4967 (p : Pattern) (ha : d62773 p = 1) (hb : d72872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d72867 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, d72867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, d72867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4966 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d72868 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, d72868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, d72868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d72869 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, d72869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, d72869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d72870 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, d72870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, d72870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d72871 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, d72871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, d72871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d72872 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, d72872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, d72872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4968 (p : Pattern) (ha : d62779 p = 1) (hb : d72878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d72811 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, d72811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4952 q ha hb
    | true =>
      simp only [d62728, d72811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4955 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d72825 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, d72825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, d72825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4958 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d72826 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, d72826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, d72826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d72840 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, d72840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, d72840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4961 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d72841 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, d72841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, d72841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d72842 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, d72842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, d72842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d72856 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, d72856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, d72856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4964 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d72857 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, d72857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, d72857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d72858 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, d72858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, d72858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d72859 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, d72859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, d72859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d72873 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, d72873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, d72873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4967 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d72874 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, d72874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, d72874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d72875 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, d72875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, d72875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d72876 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, d72876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, d72876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d72877 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, d72877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, d72877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d72878 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, d72878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, d72878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4969 (p : Pattern) (ha : d62785 p = 1) (hb : d72884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d72879 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, d72879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4968 q ha hb
    | true =>
      simp only [d62780, d72879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d72880 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, d72880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, d72880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d72881 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, d72881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, d72881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d72882 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, d72882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, d72882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d72883 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, d72883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, d72883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d72884 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, d72884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, d72884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4970 (p : Pattern) (ha : d62791 p = 1) (hb : d72890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d72885 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, d72885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4969 q ha hb
    | true =>
      simp only [d62786, d72885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d72886 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, d72886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, d72886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d72887 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, d72887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, d72887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d72888 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, d72888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, d72888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d72889 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, d72889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, d72889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d72890 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, d72890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, d72890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4971 (p : Pattern) (ha : d62797 p = 1) (hb : d72896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d72891 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, d72891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4970 q ha hb
    | true =>
      simp only [d62792, d72891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d72892 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, d72892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, d72892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d72893 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, d72893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, d72893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d72894 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, d72894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, d72894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d72895 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, d72895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, d72895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d72896 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, d72896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, d72896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4972 (p : Pattern) (ha : d62803 p = 1) (hb : d72902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d72897 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, d72897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4971 q ha hb
    | true =>
      simp only [d62798, d72897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d72898 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, d72898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, d72898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d72899 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, d72899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, d72899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d72900 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, d72900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, d72900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d72901 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, d72901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, d72901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d72902 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, d72902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, d72902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4973 (p : Pattern) (ha : d62809 p = 1) (hb : d72908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d72903 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, d72903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4972 q ha hb
    | true =>
      simp only [d62804, d72903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d72904 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, d72904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, d72904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d72905 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, d72905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, d72905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d72906 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, d72906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, d72906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d72907 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, d72907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, d72907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d72908 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, d72908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, d72908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4974 (p : Pattern) (ha : d62815 p = 1) (hb : d72914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d72909 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, d72909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4973 q ha hb
    | true =>
      simp only [d62810, d72909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d72910 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, d72910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, d72910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d72911 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, d72911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, d72911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d72912 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, d72912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, d72912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d72913 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, d72913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, d72913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d72914 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, d72914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, d72914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4975 (p : Pattern) (ha : d62821 p = 1) (hb : d72920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d72915 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, d72915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4974 q ha hb
    | true =>
      simp only [d62816, d72915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d72916 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, d72916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, d72916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d72917 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, d72917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, d72917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d72918 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, d72918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, d72918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d72919 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, d72919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, d72919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d72920 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, d72920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, d72920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4976 (p : Pattern) (ha : d213 p = 1) (hb : d51642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d4336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d51641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d213 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4977 (p : Pattern) (ha : d62704 p = 1) (hb : d73059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72617 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4976 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d73055 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d73055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d73055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2527 q = 1) (hb : d73056 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d73056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d73056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d62702 q = 1) (hb : d73057 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, d73057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, d73057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62703 q = 1) (hb : d73058 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, d73058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62703, d73058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d62704 q = 1) (hb : d73059 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, d73059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62704, d73059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h8 p ha hb
theorem andIntro4978 (p : Pattern) (ha : d2536 p = 1) (hb : d51659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d4372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d51658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4979 (p : Pattern) (ha : d62712 p = 1) (hb : d73069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4978 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d103 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d73065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d73065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d73065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2539 q = 1) (hb : d73066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d73066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d73066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62710 q = 1) (hb : d73067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, d73067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, d73067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62711 q = 1) (hb : d73068 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, d73068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62711, d73068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62712 q = 1) (hb : d73069 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, d73069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62712, d73069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4980 (p : Pattern) (ha : d62718 p = 1) (hb : d73075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62705 q = 1) (hb : d73060 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, d73060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62705, d73060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4977 q ha hb
  have h3 (q : Pattern) (ha : d62706 q = 1) (hb : d73061 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, d73061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62706, d73061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62707 q = 1) (hb : d73062 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, d73062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62707, d73062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62708 q = 1) (hb : d73063 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, d73063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62708, d73063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62709 q = 1) (hb : d73064 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, d73064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, d73064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62713 q = 1) (hb : d73070 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, d73070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62713, d73070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4979 q ha hb
  have h8 (q : Pattern) (ha : d62714 q = 1) (hb : d73071 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, d73071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62714, d73071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62715 q = 1) (hb : d73072 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, d73072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62715, d73072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62716 q = 1) (hb : d73073 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, d73073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62716, d73073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62717 q = 1) (hb : d73074 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, d73074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62717, d73074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62718 q = 1) (hb : d73075 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, d73075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62718, d73075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro4981 (p : Pattern) (ha : d2549 p = 1) (hb : d51684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d4409 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d51683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4982 (p : Pattern) (ha : d62721 p = 1) (hb : d73080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4981 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d637 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d73076 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d73076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d73076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2552 q = 1) (hb : d73077 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d73077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d73077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62719 q = 1) (hb : d73078 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, d73078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, d73078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62720 q = 1) (hb : d73079 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, d73079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62720, d73079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62721 q = 1) (hb : d73080 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, d73080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62721, d73080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4983 (p : Pattern) (ha : d62727 p = 1) (hb : d73086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d73081 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, d73081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, d73081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4982 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d73082 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, d73082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, d73082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d73083 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, d73083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, d73083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d73084 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, d73084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, d73084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d73085 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, d73085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, d73085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d73086 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, d73086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, d73086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4984 (p : Pattern) (ha : d2563 p = 1) (hb : d51710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d4447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d51709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4985 (p : Pattern) (ha : d62731 p = 1) (hb : d73092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72656 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4984 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d943 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d73088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d73088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d73088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2566 q = 1) (hb : d73089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d73089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d73089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62729 q = 1) (hb : d73090 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, d73090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, d73090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62730 q = 1) (hb : d73091 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, d73091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62730, d73091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62731 q = 1) (hb : d73092 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, d73092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62731, d73092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4986 (p : Pattern) (ha : d62737 p = 1) (hb : d73098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d73093 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, d73093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, d73093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4985 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d73094 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, d73094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, d73094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d73095 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, d73095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, d73095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d73096 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, d73096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, d73096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d73097 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, d73097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, d73097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d73098 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, d73098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, d73098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4987 (p : Pattern) (ha : d2578 p = 1) (hb : d51737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d4486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d51736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4988 (p : Pattern) (ha : d62742 p = 1) (hb : d73105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72671 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4987 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d73101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d73101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d73101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2581 q = 1) (hb : d73102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d73102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d73102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62740 q = 1) (hb : d73103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, d73103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, d73103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62741 q = 1) (hb : d73104 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, d73104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62741, d73104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62742 q = 1) (hb : d73105 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, d73105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62742, d73105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4989 (p : Pattern) (ha : d62748 p = 1) (hb : d73111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d73106 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, d73106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, d73106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4988 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d73107 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, d73107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, d73107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d73108 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, d73108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, d73108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d73109 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, d73109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, d73109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d73110 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, d73110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, d73110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d73111 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, d73111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, d73111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4990 (p : Pattern) (ha : d2594 p = 1) (hb : d51765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d4526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d51764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4991 (p : Pattern) (ha : d62754 p = 1) (hb : d73119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4990 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1831 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d73115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d73115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d73115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2597 q = 1) (hb : d73116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d73116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d73116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62752 q = 1) (hb : d73117 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, d73117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, d73117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62753 q = 1) (hb : d73118 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, d73118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62753, d73118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62754 q = 1) (hb : d73119 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, d73119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62754, d73119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4992 (p : Pattern) (ha : d62760 p = 1) (hb : d73125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d73120 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, d73120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, d73120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4991 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d73121 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, d73121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, d73121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d73122 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, d73122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, d73122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d73123 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, d73123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, d73123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d73124 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, d73124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, d73124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d73125 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, d73125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, d73125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4993 (p : Pattern) (ha : d2611 p = 1) (hb : d51794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d4567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d51793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro4994 (p : Pattern) (ha : d62767 p = 1) (hb : d73134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4993 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2309 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d73130 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d73130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d73130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2614 q = 1) (hb : d73131 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d73131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d73131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62765 q = 1) (hb : d73132 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, d73132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, d73132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62766 q = 1) (hb : d73133 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, d73133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62766, d73133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d62767 q = 1) (hb : d73134 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, d73134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62767, d73134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro4995 (p : Pattern) (ha : d62773 p = 1) (hb : d73140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d73135 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, d73135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, d73135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4994 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d73136 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, d73136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, d73136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d73137 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, d73137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, d73137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d73138 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, d73138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, d73138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d73139 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, d73139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, d73139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d73140 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, d73140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, d73140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4996 (p : Pattern) (ha : d62779 p = 1) (hb : d73146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d73087 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, d73087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4980 q ha hb
    | true =>
      simp only [d62728, d73087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4983 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d73099 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, d73099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, d73099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4986 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d73100 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, d73100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, d73100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d73112 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, d73112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, d73112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4989 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d73113 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, d73113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, d73113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d73114 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, d73114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, d73114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d73126 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, d73126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, d73126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4992 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d73127 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, d73127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, d73127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d73128 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, d73128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, d73128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d73129 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, d73129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, d73129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d73141 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, d73141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, d73141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4995 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d73142 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, d73142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, d73142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d73143 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, d73143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, d73143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d73144 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, d73144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, d73144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d73145 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, d73145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, d73145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d73146 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, d73146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, d73146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4997 (p : Pattern) (ha : d62785 p = 1) (hb : d73152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d73147 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, d73147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4996 q ha hb
    | true =>
      simp only [d62780, d73147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d73148 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, d73148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, d73148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d73149 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, d73149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, d73149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d73150 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, d73150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, d73150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d73151 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, d73151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, d73151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d73152 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, d73152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, d73152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4998 (p : Pattern) (ha : d62791 p = 1) (hb : d73158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d73153 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, d73153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4997 q ha hb
    | true =>
      simp only [d62786, d73153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d73154 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, d73154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, d73154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d73155 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, d73155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, d73155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d73156 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, d73156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, d73156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d73157 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, d73157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, d73157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d73158 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, d73158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, d73158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4999 (p : Pattern) (ha : d62797 p = 1) (hb : d73164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d73159 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, d73159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4998 q ha hb
    | true =>
      simp only [d62792, d73159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d73160 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, d73160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, d73160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d73161 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, d73161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, d73161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d73162 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, d73162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, d73162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d73163 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, d73163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, d73163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d73164 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, d73164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, d73164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
